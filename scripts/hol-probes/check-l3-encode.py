#!/usr/bin/env python3
"""Validate complete original Encode observations and kernel replay source."""
import runpy
from pathlib import Path
runpy.run_path(str(Path(__file__).resolve().parents[1] / "l3/check-encode-fixtures.py"), run_name="__main__")
