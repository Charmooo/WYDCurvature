"""Replay compiled modules through the kernel, strictly one at a time under a memory cap.
usage (from the project root, after `lake build`): python3 scripts/replay.py CAP_GB [Module ...]
With no modules, replays every module of the library (WYDCurvature.*) and AlphaCurvature.*.
`scripts/replay1.lean` is leanchecker's replayFromImports for exactly the named module: every declaration of the
.olean is sent to the kernel again.  (`leanchecker M` would also replay every module whose name starts with M, in parallel.)"""
import subprocess, sys, time, os, glob
root = os.path.dirname(os.path.dirname(os.path.abspath(__file__))); os.chdir(root)
cap = float(sys.argv[1]); mods = sys.argv[2:]
tc = open('lean-toolchain').read().strip()
env = dict(os.environ, ELAN_TOOLCHAIN=tc)
env['LEAN_PATH'] = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], env=env, capture_output=True, text=True,
                                  check=True).stdout.strip()
if not mods:
    for lib, d in (('WYDCurvature', '.lake/build/lib/lean'), ('AlphaCurvature', '../AlphaCurvature/.lake/build/lib/lean')):
        for f in sorted(glob.glob(f'{d}/{lib}/**/*.olean', recursive=True)):
            mods.append(os.path.relpath(f, d)[:-6].replace('/', '.'))
bad = 0
for m in mods:
    t = time.time(); p = subprocess.Popen(['lean', '--run', 'scripts/replay1.lean', m], env=env, stdout=subprocess.PIPE,
                                          stderr=subprocess.STDOUT, text=True); peak = 0; killed = False
    while p.poll() is None:
        r = subprocess.run(['ps', '-o', 'rss=', '-p', str(p.pid)], capture_output=True, text=True).stdout.strip()
        if r:
            peak = max(peak, int(r) / 2**20)
            if peak > cap: p.kill(); killed = True
        time.sleep(.25)
    out = p.stdout.read().strip(); ok = p.returncode == 0; bad += not ok
    print(f"{m} {'OK' if ok else 'FAILED'}{' KILLED at cap' if killed else ''} {time.time()-t:.0f}s peak rss {peak:.2f} GB {out[-200:]}", flush=True)
    if killed: break
print('modules:', len(mods), 'replay failures:', bad)
sys.exit(1 if bad else 0)
