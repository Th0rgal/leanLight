import LeanLightTests.Fixture

/-!
`lake exe leanlight-client-test [fixtures...]`: the client's decisions (`LeanLight.Driver`) on
recorded mainnet runs (`fixtures/`, `leanlight record`), offline, at the recorded clock.

The honest run: the bootstrap starts the store, every update is accepted, the store anchors at the
recorded block, its header binds, and each read gives the endpoint's word (the account fields and
storage values it sent beside its proof, which the client never reads), code its proved hash.

Then the forgeries, each refused: another checkpoint; the bootstrap past the age bound; a byte of
an update's attested header, or of its signature, changed (the update refused, the anchor not
moved by it); another block's header, or one byte of it; one byte of an account or storage
proof; one byte of the code. Exits 1 on any failure.
-/

open LeanLight.Lc LeanLight.Cli LeanLightTests.Fixture

structure Tally where
  passed : Nat := 0
  failed : Array String := #[]

def check (t : Tally) (ok : Bool) (what : String) : Tally :=
  if ok then { t with passed := t.passed + 1 } else { t with failed := t.failed.push what }

def flipByte (b : ByteArray) (i : Nat) : ByteArray :=
  if i < b.size then b.set! i (b.get! i ^^^ 1) else b

def accepted : Option Store.Verdict → Bool
  | some (.accepted _ _) => true
  | _ => false

def num (j : Json) (k : String) : Nat :=
  ((j.getObjVal? k).toOption.bind (·.getStr?.toOption) |>.bind hexNat).getD 0

def runFixture (dir : System.FilePath) (other : Option System.FilePath) (t0 : Tally) : IO Tally := do
  let f ← load dir
  let c := f.chain
  let now := f.now
  let root := f.hexOf "checkpoint"
  let o ← objects f
  let mut t := t0
  let tag := s!"{dir.fileName.getD ""}"
  -- The honest run.
  let (some s, vs) := replay c root now f o
    | return check t false s!"{tag}: the bootstrap was refused"
  t := check t (vs.all fun v => accepted v || v == some .irrelevant || v == some (.accepted false false))
    s!"{tag}: an update was refused: {vs.map (·.map verdictName)}"
  let some a := Store.anchored c s now | return check t false s!"{tag}: the store does not anchor"
  t := check t (a.header.elHash == f.hexOf "anchor_hash") s!"{tag}: anchored at another block"
  let rlp ← headerRlp f
  let some (_, h) := Driver.bindAnchor c s now rlp
    | return check t false s!"{tag}: the header does not bind"
  t := check t (toString h.number == f.get "block") s!"{tag}: the header's number"
  -- Forged chain data.
  t := check t (Driver.start c (flipByte root 0) now (f.fork "bootstrap_fork") o.bootstrap).isNone
    s!"{tag}: another checkpoint was accepted"
  t := check t (Driver.start c root (now + 15 * 24 * 3600 * 1000) (f.fork "bootstrap_fork")
    o.bootstrap).isNone s!"{tag}: a bootstrap past the age bound was accepted"
  let some s0 := Driver.start c root now (f.fork "bootstrap_fork") o.bootstrap
    | return check t false s!"{tag}: the bootstrap"
  for (what, i) in [("attested header", 20), ("signature", o.finality.size - 9)] do
    let (s1, v) := Driver.feed c s now .finality (f.fork "finality_fork") (flipByte o.finality i)
    t := check t (!accepted v) s!"{tag}: a finality update with its {what} changed was accepted"
    t := check t ((Store.anchored c s1 now).map (·.header.root) == (Store.anchored c s now).map (·.header.root))
      s!"{tag}: a refused update moved the anchor"
  if let some ch := o.chunks[0]? then
    let (_, v) := Driver.feed c s0 now .update (.digest ch.digest) (flipByte ch.ssz (ch.ssz.size - 9))
    t := check t (!accepted v) s!"{tag}: a period update with its signature changed was accepted"
  t := check t (Driver.bindAnchor c s now (flipByte rlp (rlp.size / 2))).isNone
    s!"{tag}: a header with a byte changed bound"
  if let some od := other then
    let g ← load od
    t := check t (Driver.bindAnchor c s now (← headerRlp g)).isNone
      s!"{tag}: another block's header bound"
  -- The reads.
  for r in ← reads f do
    match r.words, r.files with
    | ["block-number"], _ => pure ()
    | kind :: addrText :: _, proofFile :: rest =>
      let some addr := hexBytes addrText | t := check t false s!"{tag}: {addrText}"; continue
      let j ← readJson f proofFile
      let (nodes, slots) ← match proofParts j with
        | .ok p => pure p
        | .error e => t := check t false s!"{tag}: {proofFile}: {e}"; continue
      match Driver.read c s now rlp addr.data.toList nodes slots with
      | none => t := check t false s!"{tag}: {kind} {addrText}: the honest proof was refused"
      | some (_, acct, words) =>
        t := check t (acct.balance == num j "balance" && acct.nonce == num j "nonce")
          s!"{tag}: {kind} {addrText}: not the endpoint's account"
        let said := ((j.getObjVal? "storageProof").toOption.bind (·.getArr?.toOption)).getD #[]
        t := check t (words == said.toList.map (num · "value"))
          s!"{tag}: {kind} {addrText}: not the endpoint's words"
        -- One byte of the account proof, or of a storage proof, changed.
        t := check t (Driver.read c s now rlp addr.data.toList (flipByte nodes (nodes.size / 2)) slots).isNone
          s!"{tag}: {kind} {addrText}: a changed account proof was accepted"
        if let (k, sn) :: more := slots then
          t := check t (Driver.read c s now rlp addr.data.toList nodes
            ((k, flipByte sn (sn.size / 2)) :: more)).isNone
            s!"{tag}: {kind} {addrText}: a changed storage proof was accepted"
        if let [codeFile] := rest then
          let text ← IO.FS.readFile (f.dir / codeFile)
          let some code := hexBytes text.trimAscii.toString
            | t := check t false s!"{tag}: {codeFile}"; continue
          t := check t (Driver.codeOk acct code) s!"{tag}: {addrText}'s code was refused"
          t := check t (!Driver.codeOk acct (flipByte code (code.size / 2)))
            s!"{tag}: {addrText}: changed code was accepted"
    | _, _ => t := check t false s!"{tag}: reads.txt: {r.words}"
  return t

def main (args : List String) : IO UInt32 := do
  let dirs : List System.FilePath :=
    if args.isEmpty then ["fixtures/mainnet-fresh", "fixtures/mainnet-week"] else args.map System.FilePath.mk
  let mut t : Tally := {}
  for d in dirs do
    t ← runFixture d (dirs.find? (· != d)) t
  for e in t.failed do IO.println s!"FAIL {e}"
  IO.println s!"leanlight-client-test: {t.passed} checks passed, {t.failed.size} failed"
  return if t.failed.isEmpty then 0 else 1
