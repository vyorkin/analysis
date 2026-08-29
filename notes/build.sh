#!/bin/bash
set -e
cd "$(dirname "$0")"
latexmk -xelatex -interaction=nonstopmode -halt-on-error main.tex
