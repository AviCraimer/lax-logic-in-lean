#!/usr/bin/env python3
"""md2eml — turn a Markdown letter into a sendable MIME message (.eml).

Thunderbird's `-compose body=...` command line treats its body as plain text,
so HTML handed to it arrives as visible markup.  The fix is to build a real
RFC 5322 message instead and let the mail client parse it.

Output is multipart/alternative by default: a text/html part for clients that
render it and a text/plain part for those that do not, which is what a
correspondent's mail client expects and what keeps links clickable.

Thunderbird ignores the `X-Unsent: 1` header that tells Outlook to open a file
in compose mode (Mozilla bugs 166541 and 688284, both still open), so a .eml
opens read-only there.  Two ways on from that:

  * open it, then Message -> Edit Message As New  (Cmd-E), which gives an
    editable HTML compose window with the formatting intact; or
  * drag the .eml onto a folder in the folder pane, which imports it as a
    real message -- drop it on Drafts and it behaves like any other draft.

The Markdown subset is the one letters actually use: paragraphs, headings,
`code`, *emphasis*, **strong**, [text](url), bare URLs, blockquotes and
bullet lists.  The first `# heading` becomes the default Subject and is
dropped from the body.

Usage:
  scripts/md2eml.py path/to/letter.md \
      --to recipient@example.org --subject "..." --out path/to/letter.eml
  scripts/md2eml.py letter.md --format html --out letter.html   # HTML only

The Subject defaults to the first `# heading`, the sender to your git identity,
and the recipient is left blank unless `--to` is given — so the plain
`scripts/md2eml.py letter.md` already produces a client-ready draft.
"""

import argparse
import html as htmllib
import re
import subprocess
import sys
import textwrap
from email.message import EmailMessage
from email.utils import formatdate, make_msgid
from pathlib import Path

# Inline styles, not a <style> block: many mail clients strip <head>.
CSS_BODY = ("max-width:34em; margin:0 auto; font-family:Georgia,Palatino,serif; "
            "font-size:16px; line-height:1.62; color:#1a1a1a;")
CSS_P = "margin:0 0 1.15em 0;"
CSS_CODE = ("font-family:Menlo,Consolas,monospace; font-size:0.9em; "
            "background:#f4f4f2; padding:1px 4px; border-radius:3px;")
CSS_A = "color:#0b5cad;"
CSS_QUOTE = "margin:0 0 1.15em 1.5em; padding-left:1em; border-left:2px solid #d8d8d4; color:#444;"

URL_RE = re.compile(r"(?<![(\"'>])\bhttps?://[^\s<>()\[\]]+")


def smarten(text):
    """Straight quotes to typographic ones.

    Also spares the Thunderbird command line, whose -compose parser ends a
    quoted value at the first bare apostrophe -- though we no longer rely on
    that route, a letter simply reads better this way.
    """
    text = re.sub(r"(?<=[A-Za-z])'(?=[A-Za-z])", "’", text)   # don't, Zorn's
    text = re.sub(r'"([^"]*)"', "“\\1”", text)            # paired doubles
    text = re.sub(r"(?<!\w)'([^']*)'(?!\w)", "‘\\1’", text)
    return text


def inline(text):
    """Markdown inline markup to HTML, code spans protected from the rest."""
    spans = []

    def stash(m):
        spans.append(m.group(1))
        return f"\x00{len(spans) - 1}\x00"

    text = re.sub(r"`([^`]+)`", stash, text)
    text = smarten(text)
    text = htmllib.escape(text, quote=False)
    text = re.sub(r"\[([^\]]+)\]\(([^)]+)\)",
                  lambda m: f'<a href="{htmllib.escape(m.group(2), quote=True)}" '
                            f'style="{CSS_A}">{m.group(1)}</a>', text)
    text = re.sub(r"\*\*([^*]+)\*\*", r"<strong>\1</strong>", text)
    text = re.sub(r"(?<!\*)\*([^*]+)\*(?!\*)", r"<em>\1</em>", text)
    text = URL_RE.sub(lambda m: f'<a href="{m.group(0)}" style="{CSS_A}">{m.group(0)}</a>', text)

    def unstash(m):
        code = htmllib.escape(spans[int(m.group(1))], quote=False)
        return f'<span style="{CSS_CODE}">{code}</span>'

    return re.sub(r"\x00(\d+)\x00", unstash, text)


def md_to_html(md):
    """Block-level conversion. Returns (title, html_fragment)."""
    title, out, bullets = None, [], []

    def flush():
        if bullets:
            items = "".join(f'<li style="margin:0 0 0.4em 0;">{inline(b)}</li>' for b in bullets)
            out.append(f'<ul style="{CSS_P} padding-left:1.3em;">{items}</ul>')
            bullets.clear()

    for block in re.split(r"\n\s*\n", md.strip()):
        block = block.strip()
        if not block:
            continue
        if block.startswith("#"):
            flush()
            level = len(block) - len(block.lstrip("#"))
            heading = block.lstrip("#").strip()
            if title is None and level == 1:
                title = heading          # becomes the Subject, not body text
                continue
            size = {2: "1.3em", 3: "1.1em"}.get(level, "1em")
            out.append(f'<h{level} style="font-size:{size}; margin:1.6em 0 0.5em 0;">'
                       f"{inline(heading)}</h{level}>")
        elif block.startswith(">"):
            flush()
            quoted = " ".join(l.lstrip("> ").strip() for l in block.splitlines())
            out.append(f'<blockquote style="{CSS_QUOTE}">{inline(quoted)}</blockquote>')
        elif re.match(r"^[-*+]\s", block):
            for line in block.splitlines():
                bullets.append(re.sub(r"^[-*+]\s+", "", line.strip()))
        else:
            flush()
            para = " ".join(l.strip() for l in block.splitlines())
            out.append(f'<p style="{CSS_P}">{inline(para)}</p>')
    flush()
    return title, "\n\n".join(out)


def md_to_text(md):
    """Readable plain-text alternative: markers stripped, links spelled out."""
    out = []
    for block in re.split(r"\n\s*\n", md.strip()):
        block = " ".join(l.strip() for l in block.strip().splitlines())
        if not block:
            continue
        if block.startswith("#"):
            continue                     # the title lives in the Subject
        block = re.sub(r"\[([^\]]+)\]\(([^)]+)\)", r"\1 <\2>", block)
        block = re.sub(r"`([^`]+)`", r"\1", block)
        block = re.sub(r"\*\*([^*]+)\*\*", r"\1", block)
        block = re.sub(r"(?<!\*)\*([^*]+)\*(?!\*)", r"\1", block)
        block = re.sub(r"^[-*+]\s+", "  - ", block)
        out.append(textwrap.fill(smarten(block), width=72))
    return "\n\n".join(out) + "\n"


def wrap_document(fragment, title):
    """Standalone HTML file, for previewing in a browser."""
    return (f"<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n"
            f"<title>{htmllib.escape(title or 'Letter')}</title>\n</head>\n"
            f"<body style=\"margin:0; padding:24px; background:#ffffff;\">\n"
            f'<div id="letter-body" style="{CSS_BODY}">\n\n{fragment}\n\n</div>\n'
            f"</body>\n</html>\n")


def git_identity():
    def cfg(key, default):
        try:
            v = subprocess.run(["git", "config", "--get", key],
                               capture_output=True, text=True, timeout=5).stdout.strip()
            return v or default
        except Exception:
            return default
    return cfg("user.name", ""), cfg("user.email", "")


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("source", type=Path, help="Markdown file")
    ap.add_argument("--out", type=Path, help="output path (default: source with new suffix)")
    ap.add_argument("--to", default="", help="recipient; omitted from headers if blank")
    ap.add_argument("--from", dest="sender", default=None, help="sender (default: git config)")
    ap.add_argument("--subject", default=None, help="default: the first '# heading'")
    ap.add_argument("--format", choices=["both", "html", "plain"], default="both",
                    help="both = multipart/alternative (default); html/plain = single part")
    args = ap.parse_args()

    md = args.source.read_text(encoding="utf-8")
    title, fragment = md_to_html(md)
    subject = args.subject or title or args.source.stem
    body_html = wrap_document(fragment, subject)
    body_text = md_to_text(md)

    if args.format == "html" and args.out and args.out.suffix == ".html":
        args.out.write_text(body_html, encoding="utf-8")
        print(f"wrote {args.out}  ({len(body_html)} chars HTML)")
        return

    name, addr = git_identity()
    sender = args.sender or (f"{name} <{addr}>" if name and addr else addr)

    msg = EmailMessage()
    msg["Subject"] = subject
    if sender:
        msg["From"] = sender
    if args.to:
        msg["To"] = args.to
    msg["Date"] = formatdate(localtime=True)
    msg["Message-ID"] = make_msgid(domain=addr.split("@")[-1] if "@" in addr else "localhost")
    # Outlook opens these straight into compose; Thunderbird ignores both and
    # needs Message -> Edit Message As New. Harmless either way.
    msg["X-Unsent"] = "1"
    msg["X-Mozilla-Draft-Info"] = "internal/draft; vcard=0; receipt=0; DSN=0; uuencode=0"

    if args.format == "plain":
        msg.set_content(body_text, subtype="plain", charset="utf-8")
    elif args.format == "html":
        msg.set_content(body_html, subtype="html", charset="utf-8")
    else:
        msg.set_content(body_text, subtype="plain", charset="utf-8")
        msg.add_alternative(body_html, subtype="html", charset="utf-8")

    out = args.out or args.source.with_suffix(".eml")
    out.write_bytes(msg.as_bytes())
    print(f"wrote {out}")
    print(f"  subject : {subject}")
    print(f"  to      : {args.to or '(left blank — address it in the client)'}")
    print(f"  parts   : {msg.get_content_type()}"
          f"{' [' + ', '.join(p.get_content_type() for p in msg.iter_parts()) + ']'
             if msg.is_multipart() else ''}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
