"""Compile packaged project sources serially using the pinned local dependency cache."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

root = Path(__file__).resolve().parent
cache = Path(sys.argv[1]).resolve()
lean = Path(sys.argv[2]).resolve()
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
for line in (root/"SHA256SUMS.txt").read_text().splitlines():
    digest, name = line.split("  ", 1)
    if sha(root/name) != digest:
        raise SystemExit("Checksum mismatch: "+name)
def resolved(path):
    manifest = json.loads(path.read_bytes())
    for package in manifest["packages"]:
        package.pop("inputRev", None)  # A branch and a commit can resolve to the same rev.
    return manifest
if resolved(cache/"lake-manifest.json") != resolved(root/"lean/lake-manifest.json"):
    raise SystemExit("Dependency manifest mismatch")
if sha(lean).lower() != "ec7a472d1c12a09b0c0c718f7427c2be527b3f5f07810fdbe076c2507c7a91ea":
    raise SystemExit("Lean binary mismatch")
packages = cache/".lake/packages"
libs = []
for dep in json.loads((cache/"lake-manifest.json").read_text())["packages"]:
    path = packages/dep["name"]
    rev = subprocess.check_output(["git","-c","safe.directory="+path.as_posix(),"-C",str(path),"rev-parse","HEAD"],text=True).strip()
    if rev != dep["rev"]:
        raise SystemExit("Revision mismatch: "+str(path))
    libs.append(path/".lake/build/lib/lean")
run = Path(tempfile.mkdtemp(prefix="heat-release-replay-",dir=root.parent))
print("Replay evidence:",run,flush=True)
env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str,[run,*libs])))
order = (root/"lean/build-order.txt").read_text().splitlines()
deadline = time.monotonic()+1500
log = run/"replay.log"
for mod in order:
    rel = Path(*mod.split("."))
    obj = (run/rel).with_suffix(".olean")
    obj.parent.mkdir(parents=True,exist_ok=True)
    src = (root/"lean"/rel).with_suffix(".lean")
    # Run from the fresh root so any diagnostic files stay with this replay.
    local = (run/rel).with_suffix(".lean")
    local.write_bytes(src.read_bytes())
    p = subprocess.run([lean,"-j1","-M2048","-o",obj,local],cwd=run,env=env,
                       stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=max(1,deadline-time.monotonic()))
    with log.open("ab") as f:
        f.write((mod+"\n").encode()+p.stdout)
    if p.returncode or not obj.is_file():
        raise SystemExit("Stopped at "+mod+". See "+str(log))
audit = p.stdout.decode("utf-8",errors="replace")
for decl in ["FluxWitness400.model_benchmark","FluxWitnessC2.decoded_step_agrees",
             "FluxWitnessC3.driver223_of_wp","FluxWitnessC4.reference223",
             "FluxWitnessC2.binary64_floorEvenGrid","FluxWitnessC2.binary64_round_zero"]:
    m = re.search(re.escape("'"+decl+"' depends on axioms:")+r"\s*\[([^\]]+)\]",audit)
    if not m or set(map(str.strip,m[1].split(","))) != {"propext","Classical.choice","Quot.sound"}:
        raise SystemExit("Audit failed: "+decl)
print("PROJECT_REPLAY_ACCEPTED",log)
