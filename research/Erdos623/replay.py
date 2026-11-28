"""Replay the pinned Erdős 623 bridge with a built Formal Conjectures checkout."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys


def digest(data):
    return hashlib.sha256(data).hexdigest()


def port(name, source):
    if name == 'SingletonToCountable':
        source = source.replace('.diff (Set.finite_singleton', '.sdiff (Set.finite_singleton')
        return source.replace('haveI : Nonempty α', 'have : Nonempty α')
    if name == 'StructuralBridge':
        for before, after in [
            ('haveI : Countable', 'have : Countable'), ('letI := inst', 'let _ := inst'),
            ('noncomputable instance forbiddenStructure', 'noncomputable abbrev forbiddenStructure'),
            ('haveI : Nonempty α', 'have : Nonempty α'),
            ('letI : L.Structure α := forbiddenStructure', 'let : L.Structure α := forbiddenStructure'),
        ]:
            source = source.replace(before, after)
    return source


def prepare(formal, donor, out, manifest):
    article = manifest['article']
    entries = [(formal / article['path'], article['path'], article)]
    for row in manifest['donorModules']:
        entries.append((donor / 'lean' / row['path'], row['path'], row))
    for path, relative, row in entries:
        data = path.read_bytes()
        if digest(data) != row['inputSha256']:
            raise ValueError(f'Unexpected source digest for {path}')
        dest = out / relative
        dest.parent.mkdir(parents=True, exist_ok=True)
        output = port(dest.stem, data.decode()).encode()
        if digest(output) != row['compiledSha256']:
            raise ValueError(f'Unexpected ported digest for {relative}')
        dest.write_bytes(output)
    for name, sha in manifest['localSources'].items():
        source = Path(__file__).with_name(name)
        if digest(source.read_bytes()) != sha:
            raise ValueError(f'Unexpected local source digest for {name}')
        shutil.copyfile(source, out / name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for arg in ('formal', 'donor', 'build'):
        parser.add_argument('--'+arg, required=True, type=Path)
    parser.add_argument('--prepare-only', action='store_true')
    opts = parser.parse_args()
    manifest = json.loads(Path(__file__).with_name('manifest.json').read_text())
    out = opts.build.resolve()
    out.mkdir(parents=True, exist_ok=False)
    prepare(opts.formal.resolve(), opts.donor.resolve(), out, manifest)
    if opts.prepare_only:
        return
    tool = shutil.which('lean')
    version = subprocess.check_output([tool, '--version'], text=True)
    if 'version 4.33.1,' not in version:
        raise ValueError(version)
    pkg = opts.formal / '.lake/packages/mathlib'
    if subprocess.check_output(['git','-C',str(pkg),'rev-parse','HEAD'],text=True).strip() != manifest['mathlib']:
        raise ValueError('Unexpected Mathlib revision')
    env = dict(os.environ, LEAN_PATH=str(out)+os.pathsep+os.environ.get('LEAN_PATH', ''))
    for source in manifest['buildOrder']:
        obj = str(Path(source).with_suffix('.olean'))
        result = subprocess.run([tool,'-j1','-o',obj,source],cwd=out,env=env,text=True,
                                stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        print(result.stdout, end='')
        result.check_returncode()
        if source == 'PublicAudit.lean':
            rows = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",result.stdout)
            if {name for name, _ in rows} != set(manifest['audits']):
                raise ValueError('Incomplete axiom audit')
            for name, listed in rows:
                if not set(map(str.strip,listed.split(','))) <= {'propext','Classical.choice','Quot.sound'}:
                    raise ValueError(f'Unexpected axioms for {name}')


if __name__ == '__main__':
    main()
