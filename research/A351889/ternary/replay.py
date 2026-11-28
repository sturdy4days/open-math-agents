"""Run inside the project's pinned lake env, with proof sources next to this script."""
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
from urllib.request import urlopen

directory = Path(__file__).resolve().parent
repository = 'https://raw.githubusercontent.com/'
inputs = [
    (
        'OMAStatements/S_oeis_a351889',
        'lefttosolve2/open-math-agents/c6635296758d3877cdad0bcb4d3358a1e7507b32/statements/oeis-a351889.lean',
        '0152bcb42a27352bf464dab44ab3c9c7c472f1011821bf392dba28499d4104ec',
    ),
    (
        'PriorLift',
        'MattGaiser/open-math-agents/139cdc3b1cd7ee9382070eafddf16859331991f9/proofs/oeis-a351889.lean',
        'cc3927b5e42f4395cbd49cbeb8fd1e0dd0ec913e78e23af0a1ad87583dedf5c2',
    ),
]

lean = shutil.which('lean')
assert lean and 'version 4.33.1' in subprocess.check_output([lean, '--version'], text=True)
# Lake may use relative search-path components. Preserve their meaning before changing cwd.
paths = [str(Path(x).resolve()) for x in os.environ.get('LEAN_PATH','').split(os.pathsep) if x]
with tempfile.TemporaryDirectory(prefix='multinacci-ternary-') as temp:
    build = Path(temp)
    env = {**os.environ, 'LEAN_PATH': os.pathsep.join([str(build), *paths])}
    for module, url, sha in inputs:
        with urlopen(repository + url, timeout=60) as remote:
            source = remote.read()
        if hashlib.sha256(source).hexdigest() != sha:
            raise ValueError(f'Unexpected upstream source for {module}')
        path = build / (module + '.lean')
        path.parent.mkdir(parents=True,exist_ok=True)
        path.write_bytes(source)
    for module in ['ModuloNine','TernaryPeriods','Audit']:
        shutil.copyfile(directory / (module + '.lean'), build / (module + '.lean'))
    for module in [name for name,_,_ in inputs] + ['ModuloNine','TernaryPeriods','Audit']:
        command = [lean, '-j1', '-M9200', '-o', module + '.olean', module + '.lean']
        result = subprocess.run(command, cwd=build, env=env, text=True, check=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        print(result.stdout, end='')
        if module == 'Audit':
            lines = result.stdout.splitlines()
            assert len(lines)==8 and all(line.endswith('[propext, Classical.choice, Quot.sound]') for line in lines)
