#!/usr/bin/env python3
"""Generate the CakeML driver's help text from the pinned compiler source."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / 'cakeml/compiler/compilerScript.sml'
OUTPUT = ROOT / 'Flapjack/CakeHelp.lean'


def source_help():
    source = SOURCE.read_text(encoding='utf-8')
    start = 'val help_string = (* beginning of --help string *) ‘'
    end = '’ (* end of --help string *)'
    if source.count(start) != 1 or source.count(end) != 1:
        raise ValueError('could not uniquely locate the CakeML help string')
    text = source.split(start, 1)[1].split(end, 1)[0]
    if not text.isascii():
        raise ValueError('the CakeML help string contains non-ASCII characters')
    return text


def render():
    text = json.dumps(source_help(), ensure_ascii=True)
    return ('/-! Generated from the pinned CakeML compiler help string by\n'
            '`scripts/generate-cake-help.py`. This String is CLI infrastructure;\n'
            'it is not a reviewed port of HOL\'s mlstring declaration. -/\n'
            'namespace Flapjack.CakeHelp\n\n'
            '/-- Help text printed by the CakeML compiler driver. -/\n'
            f'def text : String := {text}\n\n'
            'end Flapjack.CakeHelp\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    generated = render()
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text() != generated:
            raise SystemExit('generated CakeML help text is out of date')
        print('CakeML help text matches the pinned source')
    else:
        OUTPUT.write_text(generated)
