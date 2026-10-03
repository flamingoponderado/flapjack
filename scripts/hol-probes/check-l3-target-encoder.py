#!/usr/bin/env python3
"""Validate complete original native assembler lowering and encoded byte lists."""
import runpy
from pathlib import Path
runpy.run_path(str(Path(__file__).resolve().parents[1]/"l3/check-target-encoder-fixtures.py"),run_name="__main__")
