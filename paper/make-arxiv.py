#!/usr/bin/env python3
r"""Build the arXiv source bundle of the paper.

The paper folder is shared by the Lax submission and arXiv. The Lax markers
(`% lax begin ...` / `% lax end`) are LaTeX comments, so both get the same PDF;
for arXiv, whose source downloads are public, this script also removes all
comments (including the markers) and `comment` environments from the
project's own .tex and .sty files. It also puts \pdfoutput=1 on the first line
of main.tex, which arXiv recommends for pdflatex papers; it is not in the
shared source because the archive derives its web view with lualatex, where
\pdfoutput is undefined.

    python3 make-arxiv.py [OUTPUT_DIR]        (default: ../arxiv)

It compiles the paper once with latexmk, takes exactly the files that the
compilation read from this folder, ships the generated main.bbl instead of the
.bib file, strips comments, compiles the stripped copy as a check, and writes
OUTPUT_DIR/arxiv-source.zip together with the unpacked sources in OUTPUT_DIR/src.
"""
import os
import re
import shutil
import subprocess
import sys
import tempfile
import zipfile

HERE = os.path.dirname(os.path.abspath(__file__))
MAIN = 'main'
OUT = os.path.abspath(sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, '..', 'arxiv'))
STRIP = ('.tex', '.sty')  # our own sources; acmart.cls is shipped unchanged


def first_comment(line):
    """Index of the first unescaped %, or -1 (as in the Lax marker rewriter)."""
    for i, c in enumerate(line):
        if c == '%':
            backslashes = len(line[:i]) - len(line[:i].rstrip('\\'))
            if backslashes % 2 == 0:
                return i
    return -1


def strip_comments(text):
    out, in_comment_env = [], False
    for line in text.split('\n'):
        if re.match(r'\s*\\begin\{comment\}', line):
            in_comment_env = True
        if in_comment_env:
            if re.match(r'\s*\\end\{comment\}', line):
                in_comment_env = False
            continue
        i = first_comment(line)
        if i < 0:
            out.append(line)
        elif line[:i].strip():
            out.append(line[:i + 1])   # keep the % so the end of line is still eaten
        # a line holding only a comment contributes nothing to TeX: drop it
    return '\n'.join(out)


def latexmk(cwd):
    r = subprocess.run(['latexmk', '-pdf', '-interaction=nonstopmode', '-halt-on-error', MAIN + '.tex'],
                       cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if r.returncode != 0:
        sys.exit('latexmk failed in %s:\n%s' % (cwd, r.stdout[-3000:]))


def pages(build_dir):
    with open(os.path.join(build_dir, MAIN + '.log'), encoding='latin-1') as f:
        m = re.search(r'Output written on .*?\((\d+) pages?', f.read(), re.S)
    return int(m.group(1))


with tempfile.TemporaryDirectory() as tmp:
    build = os.path.join(tmp, 'build')
    shutil.copytree(HERE, build, ignore=shutil.ignore_patterns('*.pdf', '*.aux', '*.log', '*.bbl', '*.blg',
                                                               '*.fls', '*.fdb_latexmk', '*.out', '*.py',
                                                               '*.kaux', '*.diagnose', '*.cut', '*.synctex.gz'),
                    dirs_exist_ok=False)
    # figures are PDFs too: copy them back
    for root, _, files in os.walk(HERE):
        for f in files:
            if f.endswith('.pdf') and root != HERE:
                rel = os.path.relpath(os.path.join(root, f), HERE)
                shutil.copy2(os.path.join(HERE, rel), os.path.join(build, rel))
    latexmk(build)

    # the files the compilation read from the project folder
    used = set()
    for line in open(os.path.join(build, MAIN + '.fls')):
        if line.startswith('INPUT '):
            path = line[6:].strip()
            full = os.path.normpath(os.path.join(build, path))
            if full.startswith(build + os.sep) and os.path.isfile(full):
                rel = os.path.relpath(full, build)
                if not rel.startswith(MAIN + '.') or rel == MAIN + '.tex':
                    used.add(rel)
    used = {u for u in used if not u.endswith(('.bib', '.bst', '.cut', '.kaux', '.diagnose'))} | {MAIN + '.bbl'}

    src = os.path.join(OUT, 'src')
    shutil.rmtree(src, ignore_errors=True)
    for rel in sorted(used):
        dst = os.path.join(src, rel)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        if rel.endswith(STRIP):
            with open(os.path.join(build, rel), encoding='utf-8') as f:
                text = strip_comments(f.read())
            if rel == MAIN + '.tex':
                text = '\\pdfoutput=1\n' + text
            with open(dst, 'w', encoding='utf-8') as f:
                f.write(text)
        else:
            shutil.copy2(os.path.join(build, rel), dst)
    leftover = [rel for rel in used if rel.endswith(STRIP) and '% lax' in open(os.path.join(src, rel)).read()]
    assert not leftover, leftover

    # check that the stripped sources compile to the same number of pages
    check = os.path.join(tmp, 'check')
    shutil.copytree(src, check)
    latexmk(check)
    n_orig, n_new = pages(build), pages(check)
    if n_orig != n_new:
        sys.exit('page count changed after stripping comments: %d -> %d' % (n_orig, n_new))

    archive = os.path.join(OUT, 'arxiv-source.zip')
    with zipfile.ZipFile(archive, 'w', zipfile.ZIP_DEFLATED) as z:
        for rel in sorted(used):
            z.write(os.path.join(src, rel), rel)
    print('%d files, %d pages -> %s' % (len(used), n_new, archive))
