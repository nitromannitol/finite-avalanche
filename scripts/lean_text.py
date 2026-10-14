"""Nesting-aware Lean comment scanner."""
import re


def checked_quote_forms(text):
    """Fail closed on quote forms this source scanner cannot classify."""
    if re.search(r"'\\?\"'|\br#*\"|«", text):
        raise ValueError('Unsupported quote literal in public source scan')
    if re.search(r'!\s*(?:/-|--)', text):
        raise ValueError('Unsupported comment at interpolation prefix')
    for match in re.finditer(r'!\s*"', text):
        i = match.end()
        while i < len(text) and text[i] != '"':
            if text[i] == '\\':
                i += 2
            elif text[i] == '{':
                end = text.find('}', i + 1)
                if end < 0 or any(x in text[i+1:end] for x in ['"', '\\', '--', '/-', '{']):
                    raise ValueError('Unsupported nested-quote/comment interpolation')
                i = end + 1
            else:
                i += 1
        if i >= len(text):
            raise ValueError('Unterminated interpolated source string')

def segments(text):
    """Yield (is_comment, exact_text). Preserve quoted strings and nested blocks."""
    checked_quote_forms(text)
    i = start = 0
    while i < len(text):
        if text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            continue
        if text.startswith('--', i) or text.startswith('/-', i):
            if i > start:
                yield False, text[start:i]
            begin = i
            if text.startswith('--', i):
                end = text.find('\n', i)
                i = len(text) if end < 0 else end
            else:
                i += 2
                depth = 1
                while i < len(text) and depth:
                    if text.startswith('/-', i):
                        depth += 1
                        i += 2
                    elif text.startswith('-/', i):
                        depth -= 1
                        i += 2
                    else:
                        i += 1
                if depth:
                    raise ValueError('Unterminated Lean block comment')
            yield True, text[begin:i]
            start = i
            continue
        i += 1
    if start < len(text):
        yield False, text[start:]

def residue(text):
    return ''.join((''.join('\n' if c == '\n' else ' ' for c in t)
                    if comment else t) for comment, t in segments(text))
