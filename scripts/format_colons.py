#!/usr/bin/env python3
"""
Форматирует двоеточия в аннотациях типов Lean 4:
  x:Type  ->  x : Type
  x: Type ->  x : Type

Пропускает блочные комментарии (/-  ... -/) и строки-комментарии (-- ...).
Не трогает := и ::.
"""

import re
import sys


def format_colons(path: str) -> None:
    with open(path, "r") as f:
        content = f.read()

    lines = content.split("\n")
    result = []
    in_block_comment = False

    for line in lines:
        # Отслеживаем блочные комментарии
        if in_block_comment:
            result.append(line)
            if "-/" in line:
                in_block_comment = False
            continue

        if "/-" in line:
            result.append(line)
            if "-/" not in line:
                in_block_comment = True
            continue

        # Строки-комментарии не трогаем
        if line.lstrip().startswith("--"):
            result.append(line)
            continue

        # Проход 1: добавляем пробел перед : если его нет (пропускаем :=, ::)
        new_line = re.sub(r"(?<!\s):(?![=:])", r" :", line)
        # Проход 2: добавляем пробел после : если его нет
        new_line = re.sub(r":(?![\s=:])", r": ", new_line)

        result.append(new_line)

    output = "\n".join(result)
    with open(path, "w") as f:
        f.write(output)

    print(f"Formatted: {path}")


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: format_colons.py <file.lean> [file2.lean ...]")
        sys.exit(1)

    for path in sys.argv[1:]:
        format_colons(path)
