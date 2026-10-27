from pathlib import Path
import hashlib, json


def is_block_comment(text):
    if not text.startswith("/-") or not text.endswith("-/"):
        return False
    depth, i = 0, 0
    while i < len(text):
        pair = text[i:i+2]
        if pair == "/-":
            depth += 1
            i += 2
        elif pair == "-/":
            depth -= 1
            i += 2
            if depth < 0 or (depth == 0 and i != len(text)):
                return False
        else:
            i += 1
    return depth == 0


root = Path(__file__).resolve().parents[1]
manifest = json.loads((root/'verification/original-lean-sha256.json').read_text(encoding='utf-8-sig'))
certificate = root/'verification/comment-only-edits.json'
edits = json.loads(certificate.read_text(encoding='utf-8-sig'))['edits'] if certificate.exists() else {}
for name, expected in manifest.items():
    data = (root/'lean'/name).read_bytes()
    actual = hashlib.sha256(data).hexdigest()
    if actual == expected:
        continue
    if name not in edits:
        raise SystemExit(f'Original Lean source changed: {name}')
    edit = edits[name]
    if edit['original_sha256'] != expected or edit['current_sha256'] != actual:
        raise SystemExit(f'Comment-edit file hashes do not match: {name}')
    before, after = edit['before'], edit['after']
    if not is_block_comment(before) or not is_block_comment(after):
        raise SystemExit(f'Edit is not confined to one block comment: {name}')
    before, after = before.encode('utf-8'), after.encode('utf-8')
    if data.count(after) != 1:
        raise SystemExit(f'Comment location is ambiguous: {name}')
    if hashlib.sha256(data.replace(after, before, 1)).hexdigest() != expected:
        raise SystemExit(f'Code outside the documented comment changed: {name}')
baseline = root/'verification/reference.zip'
if hashlib.sha256(baseline.read_bytes()).hexdigest() != '3dfcdee24cbebfdbb9e5496295a797a52d7c4718e020808b8e0f36389b5a1fc1':
    raise SystemExit('Frozen reference archive differs from the trusted specification.')
print(f'PASS: {len(manifest):,} original Lean sources preserved, allowing {len(edits)} documented comment-only corrections; frozen specification matches.')
