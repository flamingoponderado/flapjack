#!/usr/bin/env python3
"""Generate CakeML's feature-query table from the pinned Pancake NEWS file."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
NEWS = ROOT / 'cakeml/pancake/NEWS.md'
OUTPUT = ROOT / 'Flapjack/CakeFeatures.lean'


def feature_events():
    events = []
    suffix = '`</sub>'
    prefixes = {'<sub>Feature enabled: `': True, '<sub>Feature disabled: `': False}
    for line in NEWS.read_text(encoding='utf-8').splitlines():
        if not line.startswith('<sub>'):
            continue
        if not line.endswith(suffix):
            raise ValueError('malformed Pancake feature line: ' + line)
        for prefix, enabled in prefixes.items():
            if line.startswith(prefix):
                name = line[len(prefix):-len(suffix)]
                if not name.isascii():
                    raise ValueError('non-ASCII Pancake feature name')
                events.append((name, enabled))
                break
        else:
            raise ValueError('malformed Pancake feature line: ' + line)
    # newsScript.sml checks that consecutive occurrences of a feature alternate.
    seen = {}
    for name, enabled in events:
        if name in seen and seen[name] == enabled:
            raise ValueError('feature enabled or disabled twice in a row: ' + name)
        seen[name] = enabled
    return events


def render():
    latest = {}
    for name, enabled in feature_events():
        if name not in latest:
            latest[name] = enabled
    names = ', '.join(json.dumps(name) for name, enabled in latest.items() if enabled)
    return ('/-! Generated from pinned Pancake feature history by\n'
            '`scripts/generate-cake-features.py`. This String-backed table is\n'
            'CLI infrastructure, not a reviewed HOL mlstring port. -/\n'
            'namespace Flapjack.CakeFeatures\n\n'
            '/-- Whether the pinned compiler advertises a feature. -/\n'
            f'def enabled (name : String) : Bool := [{names}].contains name\n\n'
            'end Flapjack.CakeFeatures\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    generated = render()
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text() != generated:
            raise SystemExit('generated CakeML feature table is out of date')
        print('CakeML feature table matches the pinned source')
    else:
        OUTPUT.write_text(generated)
