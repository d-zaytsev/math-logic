import argparse
import ast
import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess


CHECKS = {
  "sort": [("sort.c", "check", ["-DLEN=6", "--unwind", "8"])],
  "hacks": [("hacks.c", f"check{i}", ["--unwind", "35"]) for i in (1, 2, 3)],
  "strfind": [("strfind.c", "main", ["-DLEN=10", "--unwind", "12"])],
}

POINTS = {"sort": 1, "hacks": 1, "strfind": 3, "crc": 3}


def run_cbmc(filename, function, options, timeout=None):
  command = ["cbmc", str(filename), "--function", function,
             "--unwinding-assertions", "--verbosity", "8"] + options
  print("Running:", " ".join(command), flush=True)
  return subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=timeout)


def check_assertions(name, directory):
  score = 0
  for filename, function, options in CHECKS[name]:
    result = run_cbmc(directory / filename, function, options)
    output = result.stdout
    assertion = f"[{function}.assertion."
    has_assertion = any(line.startswith(assertion) for line in output.splitlines())
    vcc = re.search(r"Generated \d+ VCC\(s\), (\d+) remaining after simplification", output)
    ok = (result.returncode == 0 and "VERIFICATION SUCCESSFUL" in output
          and has_assertion and vcc is not None and int(vcc.group(1)) > 0)
    if not ok:
      print(output)
      if not has_assertion:
        print(f"Не найдено пользовательское утверждение {assertion}*")
      elif vcc is not None and int(vcc.group(1)) == 0:
        print("Все проверки упростились до истины: проверьте, что спецификация не пустая.")
    print(f"{name}/{function}: {'OK' if ok else 'НЕ ПРОЙДЕНО'}")
    score += POINTS[name] * int(ok)
  return score


def trace_buffer(output, length):
  values = {}
  for line in output.splitlines():
    array = re.search(r"\bbuf=\{([^}]*)\}", line)
    if array:
      parts = re.findall(r"'(?:\\.|[^'\\])*'|-?\d+", array.group(1))
      for i, part in enumerate(parts):
        if part.startswith("'"):
          try:
            values[i] = ord(ast.literal_eval(part))
          except (ValueError, SyntaxError, TypeError):
            return None
        else:
          values[i] = int(part) & 255
    element = re.search(r"\bbuf\[(\d+)l?\]=(-?\d+|'(?:\\.|[^'\\])*')", line)
    if element:
      index, value = element.groups()
      try:
        values[int(index)] = ord(ast.literal_eval(value)) if value.startswith("'") else int(value) & 255
      except (ValueError, SyntaxError, TypeError):
        return None
  if any(i not in values for i in range(length)):
    return None
  return bytes(values[i] for i in range(length))


def check_crc(directory):
  path = directory / "crc64.c"
  score = 0
  try:
    result = run_cbmc(path, "check_unique", ["-DSTRLEN=3", "--unwind", "5"], timeout=30)
    output = result.stdout
    vcc = re.search(r"Generated \d+ VCC\(s\), (\d+) remaining after simplification", output)
    ok = (result.returncode == 0 and "VERIFICATION SUCCESSFUL" in output
          and re.search(r"^\[check_unique\.assertion\.\d+\].*: SUCCESS$", output, re.MULTILINE)
          and vcc is not None and int(vcc.group(1)) > 0)
    if not ok:
      print(output)
    print(f"crc/check_unique: {'OK' if ok else 'НЕ ПРОЙДЕНО'}")
    score += int(bool(ok))
  except subprocess.TimeoutExpired:
    print("crc/check_unique: превышено время проверки (30 секунд)")

  digest = hashlib.blake2b(b"abc").hexdigest()
  for length in range(1, 21):
    try:
      result = run_cbmc(path, "check_decode", [f"-DSTRLEN={length}", "--unwind", str(length + 2), "--trace"], timeout=30)
    except subprocess.TimeoutExpired:
      print(f"crc/check_decode: превышено время проверки при длине {length} (30 секунд); остальные длины не проверены")
      break
    output = result.stdout
    assertions = re.findall(r"^\[check_decode\.assertion\.\d+\].*: (SUCCESS|FAILURE)$", output, re.MULTILINE)
    failures = re.findall(r"^\[([^\]]+)\].*: FAILURE$", output, re.MULTILINE)
    if not assertions:
      print("crc/check_decode: не найдено утверждение для поиска сообщения")
      break
    if result.returncode == 0 and not failures and "VERIFICATION SUCCESSFUL" in output:
      continue
    message = trace_buffer(output, length)
    if (result.returncode == 10 and len(failures) == 1
        and failures[0].startswith("check_decode.assertion.")
        and message is not None and hashlib.blake2b(message).hexdigest() == digest):
      print("crc/check_decode: OK")
      score += 2
      break
    print(output)
    print(f"crc/check_decode: ошибка проверки или неверное сообщение при длине {length}")
    break
  else:
    print("crc/check_decode: сообщение не найдено для длин от 1 до 20")
  return score


def main():
  parser = argparse.ArgumentParser(description="Проверка заданий практики CBMC")
  parser.add_argument("task", nargs="?", default="all", choices=["all", "sort", "hacks", "strfind", "crc"])
  args = parser.parse_args()
  if shutil.which("cbmc") is None:
    print("CBMC не найден в PATH. Установите CBMC и проверьте команду cbmc --version.")
    return 1
  os.chdir(Path(__file__).resolve().parent)
  directory = Path(".")
  names = ["sort", "hacks", "strfind", "crc"] if args.task == "all" else [args.task]
  score = 0
  maximum = sum(POINTS[name] * (1 if name == "crc" else len(CHECKS[name])) for name in names)
  try:
    for name in names:
      score += check_crc(directory) if name == "crc" else check_assertions(name, directory)
  except FileNotFoundError as error:
    print(f"Не найден файл или программа: {error.filename}")
    return 1
  print(f"\nНабрано баллов: {score} из {maximum}")
  return 0 if score == maximum else 1


if __name__ == "__main__":
  raise SystemExit(main())
