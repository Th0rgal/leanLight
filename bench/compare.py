#!/usr/bin/env python3
"""leanLight vs Helios, on the same endpoints and the same checkpoint.

For each endpoint set and each round:

1. The checkpoint: the consensus node's finalized root now (or one `--age-periods` sync-committee
   periods older, the first slot of an epoch that many periods back). Both clients get it.
2. Helios (`helios ethereum -c CL -e EL -w CHECKPOINT`, a fresh data dir) is started and polled
   with `eth_blockNumber` until it answers (it refuses while "out of sync"): its sync time, its
   CPU time and peak RSS at that moment.
3. `leanlight --json --checkpoint CHECKPOINT queries FILE`: its sync time (bootstrap, updates,
   finality and optimistic updates), then each read at its anchored block N, with the time spent
   on the network and verifying. CPU time and peak RSS of it and its curl children.
4. Each read is asked of Helios at block N (and, when Helios no longer holds N, at "latest"), and
   of the execution endpoint directly at N, unverified, as the reference. Values are compared.

The order of the two clients alternates between rounds. Results go to a JSON file, and a
Markdown summary to standard output.
"""

import argparse
import json
import os
import resource
import shutil
import socket
import subprocess
import sys
import tempfile
import time
import urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))


def http_json(url, data=None, timeout=60):
    req = urllib.request.Request(url, data=json.dumps(data).encode() if data else None,
                                 headers={"Content-Type": "application/json",
                                          "Accept": "application/json",
                                          "User-Agent": "leanlight-bench"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return json.loads(r.read())


def rpc(url, method, params, timeout=60):
    r = http_json(url, {"jsonrpc": "2.0", "id": 1, "method": method, "params": params}, timeout)
    if "error" in r:
        raise RuntimeError(f"{method}: {r['error']}")
    return r["result"]


def free_port():
    s = socket.socket()
    s.bind(("127.0.0.1", 0))
    p = s.getsockname()[1]
    s.close()
    return p


def checkpoint(cl, age_periods):
    if age_periods == 0:
        return http_json(f"{cl}/eth/v1/beacon/headers/finalized")["data"]["root"]
    fin = int(http_json(f"{cl}/eth/v1/beacon/headers/finalized")["data"]["header"]["message"]["slot"])
    slot = (fin // 32) * 32 - age_periods * 8192
    for _ in range(32):  # step forward past empty slots, an epoch at most
        try:
            return http_json(f"{cl}/eth/v1/beacon/headers/{slot}")["data"]["root"]
        except Exception:
            slot += 32
    raise RuntimeError("no checkpoint block found")


def proc_cpu_rss(pid):
    with open(f"/proc/{pid}/stat") as f:
        parts = f.read().rsplit(")", 1)[1].split()
    tick = os.sysconf("SC_CLK_TCK")
    cpu = (int(parts[11]) + int(parts[12])) / tick
    rss = 0
    with open(f"/proc/{pid}/status") as f:
        for line in f:
            if line.startswith("VmHWM:"):
                rss = int(line.split()[1])  # kB
    return cpu, rss


def keccak(hexstr):
    return subprocess.run([os.path.expanduser("~/.foundry/bin/cast"), "keccak", hexstr],
                          capture_output=True, text=True, check=True).stdout.strip()


class Helios:
    def __init__(self, binary, network, cl, el, cp, log):
        self.port = free_port()
        self.dir = tempfile.mkdtemp(prefix="helios-bench.")
        self.url = f"http://127.0.0.1:{self.port}"
        self.t0 = time.monotonic()
        self.p = subprocess.Popen([binary, "ethereum", "-n", network, "-c", cl, "-e", el, "-w", cp,
                                   "-p", str(self.port), "-d", self.dir],
                                  stdout=log, stderr=subprocess.STDOUT)

    def wait_ready(self, limit=300):
        last = None
        while time.monotonic() - self.t0 < limit:
            if self.p.poll() is not None:
                raise RuntimeError(f"helios exited {self.p.returncode}")
            try:
                n = int(rpc(self.url, "eth_blockNumber", [], timeout=5), 16)
                ready = time.monotonic() - self.t0
                cpu, rss = proc_cpu_rss(self.p.pid)
                return {"sync_s": ready, "cpu_s": cpu, "rss_kb": rss, "block": n}
            except Exception as e:  # not listening yet, or out of sync
                last = str(e)
            time.sleep(0.05)
        raise RuntimeError(f"helios not ready after {limit} s: {last}")

    def stop(self):
        self.p.terminate()
        try:
            self.p.wait(10)
        except subprocess.TimeoutExpired:
            self.p.kill()
        shutil.rmtree(self.dir, ignore_errors=True)


def run_leanlight(binary, network, cl, el, cp, queries):
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    t0 = time.monotonic()
    out = subprocess.run([binary, "--network", network, "--consensus-rpc", cl, "--execution-rpc", el,
                          "--checkpoint", cp, "--json", "queries", queries],
                         capture_output=True, text=True)
    wall = time.monotonic() - t0
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    lines = [json.loads(l) for l in out.stdout.splitlines() if l.startswith("{")]
    if out.returncode != 0 or not lines:
        raise RuntimeError(f"leanlight failed ({out.returncode}): {out.stderr.strip()[-500:]}")
    sync = lines[0]
    return {
        "wall_s": wall,
        "sync_s": sync["ms"] / 1000,
        "sync_net_s": sync["net_ms"] / 1000,
        "sync_verify_s": sync["verify_ms"] / 1000,
        "updates": sync["updates"],
        "refused": sync["refused"],
        "cpu_s": (after.ru_utime - before.ru_utime) + (after.ru_stime - before.ru_stime),
        "rss_kb": after.ru_maxrss,
        "anchor": lines[1],
        "reads": lines[2:],
    }


def ask(url, q, tag):
    kind = q["q"]
    if kind == "block-number":
        return int(rpc(url, "eth_blockNumber", []), 16)
    if kind == "balance":
        return int(rpc(url, "eth_getBalance", [q["addr"], tag]), 16)
    if kind == "nonce":
        return int(rpc(url, "eth_getTransactionCount", [q["addr"], tag]), 16)
    if kind == "code":
        return keccak(rpc(url, "eth_getCode", [q["addr"], tag]))
    if kind == "storage":
        return [int(rpc(url, "eth_getStorageAt", [q["addr"], s, tag]), 16) for s in q["slots"]]
    raise ValueError(kind)


def leanlight_value(q):
    v = q["value"]
    if q["q"] == "block-number":
        return int(v)
    if q["q"] in ("balance", "nonce"):
        return int(v, 16)
    if q["q"] == "code":
        return v
    return [int(x, 16) for x in v]


def compare_reads(ll, helios_url, el):
    block = ll["anchor"]["block"]
    tag = hex(block)
    rows = []
    for q in ll["reads"]:
        row = {"q": q.get("q"), "addr": q.get("addr"), "slots": q.get("slots"),
               "leanlight_ms": q.get("ms"), "leanlight_net_ms": q.get("net_ms"),
               "leanlight_verify_ms": q.get("verify_ms")}
        if "error" in q:
            row["leanlight_error"] = q["error"]
            rows.append(row)
            continue
        row["leanlight"] = leanlight_value(q)
        try:
            row["reference"] = ask(el, q, tag) if q["q"] != "block-number" else block
        except Exception as e:
            row["reference_error"] = str(e)
        for t in (tag, "latest"):
            t0 = time.monotonic()
            try:
                row["helios"] = ask(helios_url, q, t)
                row["helios_ms"] = (time.monotonic() - t0) * 1000
                row["helios_tag"] = t
                break
            except Exception as e:
                row["helios_error"] = str(e)
        if q["q"] == "block-number":
            row["helios_tag"] = "latest"
        rows.append(row)
    return rows


def per_read(results):
    """Median per-read latency, leanlight (one process, curl per request) and helios (JSON-RPC)."""
    import statistics
    by = {}
    for r in results:
        for x in r.get("reads", []):
            if x["q"] == "block-number" or "leanlight_error" in x:
                continue
            d = by.setdefault(x["q"], {"leanlight": [], "helios": []})
            d["leanlight"].append(x["leanlight_ms"])
            if "helios_ms" in x:
                d["helios"].append(x["helios_ms"])
    print()
    print("| read | leanlight median ms | helios median ms | samples |")
    print("|---|---|---|---|")
    for q, d in by.items():
        h = f"{statistics.median(d['helios']):.0f}" if d["helios"] else "-"
        print(f"| {q} | {statistics.median(d['leanlight']):.0f} | {h} | {len(d['leanlight'])} |")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--network", default="mainnet")
    ap.add_argument("--endpoints", action="append", required=True,
                    help="NAME,CONSENSUS_URL,EXECUTION_URL (repeatable)")
    ap.add_argument("--queries", default=os.path.join(HERE, "mainnet.queries"))
    ap.add_argument("--rounds", type=int, default=3)
    ap.add_argument("--age-periods", type=int, default=0)
    ap.add_argument("--leanlight", default=os.path.join(HERE, "..", ".lake", "build", "bin", "leanlight"))
    ap.add_argument("--helios", required=True)
    ap.add_argument("--ready-limit", type=float, default=180,
                    help="seconds Helios gets to answer eth_blockNumber")
    ap.add_argument("--out", required=True)
    args = ap.parse_args()

    results = []
    for spec in args.endpoints:
        name, cl, el = spec.split(",")
        for r in range(args.rounds):
            cp = checkpoint(cl, args.age_periods)
            res = {"endpoints": name, "consensus": cl, "execution": el, "round": r,
                   "checkpoint": cp, "age_periods": args.age_periods}
            print(f"[{name} round {r}] checkpoint {cp}", file=sys.stderr)
            log = open(args.out + f".helios-{name}-{r}.log", "w")
            order = ["helios", "leanlight"] if r % 2 == 0 else ["leanlight", "helios"]
            res["order"] = order
            h = None
            try:
                for who in order:
                    if who == "helios":
                        h = Helios(args.helios, args.network, cl, el, cp, log)
                        try:
                            res["helios"] = h.wait_ready(args.ready_limit)
                        except Exception as e:
                            res["helios"] = {"error": str(e)}
                    else:
                        try:
                            res["leanlight"] = run_leanlight(args.leanlight, args.network, cl, el, cp,
                                                             args.queries)
                        except Exception as e:
                            res["leanlight"] = {"error": str(e)}
                if "error" not in res["leanlight"] and "error" not in res["helios"]:
                    res["reads"] = compare_reads(res["leanlight"], h.url, el)
            finally:
                if h:
                    h.stop()
                log.close()
            results.append(res)
            json.dump(results, open(args.out, "w"), indent=1)
    summarize(results)
    per_read(results)


def summarize(results):
    print("| endpoints | round | checkpoint age | helios sync s | helios CPU s | helios RSS MB |"
          " leanlight sync s (net / verify) | leanlight CPU s | leanlight RSS MB |"
          " = helios at block N | = endpoint at N | leanlight errors | helios not at N |")
    print("|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    for r in results:
        h, l = r.get("helios", {}), r.get("leanlight", {})
        reads = r.get("reads", [])
        tag = hex(l["anchor"]["block"]) if "anchor" in l else None
        at_n = [x for x in reads if x.get("helios_tag") == tag]
        same = sum(1 for x in at_n if x.get("leanlight") == x["helios"])
        ref = sum(1 for x in reads if "reference" in x and x.get("leanlight") == x["reference"])
        errs = sum(1 for x in reads if "leanlight_error" in x)
        hs = f"{h['sync_s']:.2f}" if "sync_s" in h else h.get("error", "?")[:40]
        ls = (f"{l['sync_s']:.2f} ({l['sync_net_s']:.2f} / {l['sync_verify_s']:.2f})"
              if "sync_s" in l else l.get("error", "?")[:40])
        print(f"| {r['endpoints']} | {r['round']} | {r['age_periods']} periods | {hs} | "
              f"{h.get('cpu_s', 0):.2f} | {h.get('rss_kb', 0) / 1024:.0f} | {ls} | "
              f"{l.get('cpu_s', 0):.2f} | {l.get('rss_kb', 0) / 1024:.0f} | "
              f"{same}/{len(at_n)} | {ref}/{len(reads)} | {errs} | {len(reads) - len(at_n)} |")


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "--summarize":
        rs = json.load(open(sys.argv[2]))
        summarize(rs)
        per_read(rs)
    else:
        main()
