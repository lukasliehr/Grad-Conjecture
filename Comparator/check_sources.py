#!/usr/bin/env python3
"""Check the library source hashes and the showcase comparison copy."""
import csv
import hashlib
from pathlib import Path

root = Path(__file__).resolve().parent.parent
with (root / 'LeanCode/MODULES.tsv').open() as stream:
    rows = list(csv.DictReader(stream, delimiter='\t'))
assert len(rows) == 5839
assert len({r['module'] for r in rows}) == len(rows)
paths = {r['path'] for r in rows}
assert paths == {p.relative_to(root).as_posix() for p in (root / 'LeanCode').rglob('*.lean')}
for row in rows:
    content = (root / row['path']).read_bytes()
    assert hashlib.sha256(content).hexdigest() == row['sha256'], row['path']
surface = (root / 'Showcase.lean').read_text()
surface = surface.replace('Grad.Showcase', 'Grad.ShowcaseSurface.Public')
surface = surface.replace('Grad.MainTarget', 'Grad.ShowcaseSurface.MainTarget')
assert surface == (root / 'Comparator/Showcase_DefinitionSurface.lean').read_text(), \
    'Regenerate Showcase_DefinitionSurface.lean after changing Showcase.lean'
print('PROJECT_SOURCE_HASHES_MATCH 5839')
print('DEFINITION_SURFACE_CURRENT')
