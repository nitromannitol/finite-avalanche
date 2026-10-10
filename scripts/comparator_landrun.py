#!/usr/bin/env python3
"""Preserve child argv across the pinned Landrun CLI's outer option parser."""
from pathlib import Path
import os
import sys

BOOL_FLAGS = {'--best-effort', '-ldd', '-add-exec'}
VALUE_FLAGS = {'--ro', '--rw', '--rox', '--rwx', '--env'}


def separated_arguments(args):
    """Insert only the outer separator; preserve every original token and order."""
    index = 0
    while index < len(args):
        token = args[index]
        if token == '--':
            if index + 1 == len(args) or not args[index + 1] or args[index + 1].startswith('-'):
                raise ValueError('missing sandboxed executable after separator')
            return list(args)
        if token in BOOL_FLAGS:
            index += 1
        elif token in VALUE_FLAGS:
            if index + 1 == len(args) or not args[index + 1] or args[index + 1].startswith('-'):
                raise ValueError('missing value for sandbox option ' + token)
            index += 2
        elif not token or token.startswith('-'):
            raise ValueError('unsupported sandbox option ' + repr(token))
        else:
            return [*args[:index], '--', *args[index:]]
    raise ValueError('missing sandboxed executable')


def main():
    value = os.environ.get('COMPARATOR_REAL_LANDRUN', '')
    backend = Path(value)
    if not value or not backend.is_absolute() or backend.is_symlink() or not backend.is_file():
        raise ValueError('COMPARATOR_REAL_LANDRUN must name the verified regular absolute binary')
    if backend.resolve() == Path(__file__).resolve() or not os.access(backend, os.X_OK):
        raise ValueError('invalid Landrun backend executable')
    args = separated_arguments(sys.argv[1:])
    os.execv(str(backend), [str(backend), *args])


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError) as error:
        print('comparator landrun adapter: ' + str(error), file=sys.stderr)
        raise SystemExit(2) from error
