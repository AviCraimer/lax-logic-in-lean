#!/usr/bin/env python3
"""Minimal OpenAI Batch API client (stdlib only).

Batch is half price, and for a benchmark sweep the latency is irrelevant --
nothing downstream needs an answer in the next minute.  The trade-off is a
completion window of up to 24 hours, so this is the wrong mode for anything
interactive; `harness.py --now` exists for that.

Submission and collection are deliberately separable: a sweep can be submitted,
the machine shut down, and the results collected the next day with
`--batch-resume <id>`.
"""
from __future__ import annotations

import json
import time
import urllib.error
import urllib.request
import uuid
from pathlib import Path

API = "https://api.openai.com/v1"


def _req(path: str, key: str, data=None, method=None, ctype="application/json"):
    req = urllib.request.Request(
        API + path,
        data=data,
        headers={"Authorization": f"Bearer {key}",
                 **({"Content-Type": ctype} if data is not None else {})},
        method=method,
    )
    with urllib.request.urlopen(req, timeout=180) as r:
        return json.loads(r.read())


def upload_jsonl(lines: list[dict], key: str) -> str:
    """Upload a JSONL batch input file (multipart/form-data by hand)."""
    payload = "\n".join(json.dumps(o) for o in lines).encode()
    boundary = "----batch" + uuid.uuid4().hex
    parts = []
    parts.append(f'--{boundary}\r\nContent-Disposition: form-data; name="purpose"\r\n\r\nbatch\r\n'.encode())
    parts.append(
        f'--{boundary}\r\nContent-Disposition: form-data; name="file"; '
        f'filename="batch.jsonl"\r\nContent-Type: application/jsonl\r\n\r\n'.encode()
        + payload + b"\r\n")
    parts.append(f"--{boundary}--\r\n".encode())
    body = b"".join(parts)
    out = _req("/files", key, data=body,
               ctype=f"multipart/form-data; boundary={boundary}")
    fid = out["id"]
    # The file is not usable the instant it is created: creating a batch
    # against it too early fails with "Cannot find file ...". Wait for the
    # server to report it processed.
    for _ in range(60):
        rec = _req(f"/files/{fid}", key)
        if rec.get("status") == "processed":
            return fid
        if rec.get("status") == "error":
            raise RuntimeError(f"upload failed: {rec.get('status_details')}")
        time.sleep(2)
    raise RuntimeError(f"file {fid} not processed in time")


def create(file_id: str, key: str, window: str = "24h") -> dict:
    return _req("/batches", key, data=json.dumps({
        "input_file_id": file_id,
        "endpoint": "/v1/chat/completions",
        "completion_window": window,
    }).encode())


def status(batch_id: str, key: str) -> dict:
    return _req(f"/batches/{batch_id}", key)


def fetch_output(file_id: str, key: str) -> list[dict]:
    req = urllib.request.Request(f"{API}/files/{file_id}/content",
                                 headers={"Authorization": f"Bearer {key}"})
    with urllib.request.urlopen(req, timeout=300) as r:
        raw = r.read().decode()
    return [json.loads(l) for l in raw.splitlines() if l.strip()]


def wait(batch_id: str, key: str, poll: int = 30, limit: int | None = None,
         log=print) -> dict:
    """Poll until terminal. `limit` seconds; None waits indefinitely."""
    t0 = time.monotonic()
    seen = None
    while True:
        b = status(batch_id, key)
        st = b.get("status")
        if st != seen:
            c = b.get("request_counts", {}) or {}
            log(f"  batch {batch_id}: {st} "
                f"({c.get('completed',0)}/{c.get('total',0)} done, "
                f"{c.get('failed',0)} failed)")
            seen = st
        if st in ("completed", "failed", "expired", "cancelled"):
            return b
        if limit is not None and time.monotonic() - t0 > limit:
            log(f"  still {st} after {limit}s; resume later with "
                f"--batch-resume {batch_id}")
            return b
        time.sleep(poll)
