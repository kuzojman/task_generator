"""Самопроверка генераторов ЕГЭ № 14 (системы счисления).

В проекте нет тестовой инфраструктуры (pytest не используется), поэтому
проверки живут в одном запускаемом модуле.

Запуск из корня проекта::

    python -m INFORMATIC.EGE.D_Sys_Is.numsys_selfcheck

Запуск из этого каталога::

    python numsys_selfcheck.py

Код возврата: 0 -- все проверки прошли, 1 -- есть падения.
"""

import os
import random
import sys
import time

try:
    from . import numsys_core
except ImportError:  # прямой запуск файлом, без пакетного импорта
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import numsys_core


CORE = numsys_core


def reference_digits(value, base):
    """Независимая реализация: запись числа от старшей цифры к младшей."""
    if value == 0:
        return "0"
    chars = CORE.DIGIT_CHARS
    result = ""
    while value:
        value, remainder = divmod(value, base)
        result = chars[remainder] + result
    return result


def _raises(exception, callable_object, *args, **kwargs):
    """Верно ли, что вызов поднимает именно `exception`."""
    try:
        callable_object(*args, **kwargs)
    except exception:
        return True
    except Exception:
        return False
    return False


def core_cases():
    """Проверки ядра: 20+ «ручных» примеров и 300 случайных сверок."""
    core = CORE
    cases = []

    def case(description, condition):
        cases.append((description, bool(condition)))

    # --- ручные примеры ---------------------------------------------------
    case("digits_of(0, 2) -> [0]", core.digits_of(0, 2) == [0])
    case("digits_of(255, 16) -> [15, 15]", core.digits_of(255, 16) == [15, 15])
    case("digits_msd(255, 16) -> [15, 15]",
         core.digits_msd(255, 16) == [15, 15])
    case("to_base_string(255, 16) -> 'FF'",
         core.to_base_string(255, 16) == "FF")
    case("to_base_string(255, 16, upper=False) -> 'ff'",
         core.to_base_string(255, 16, upper=False) == "ff")
    case("to_base_string(0, 7) -> '0'", core.to_base_string(0, 7) == "0")
    case("to_base_string(1000, 2) == bin(1000)[2:]",
         core.to_base_string(1000, 2) == bin(1000)[2:])
    case("value_of([15, 15], 16) == 255", core.value_of([15, 15], 16) == 255)
    case("value_of(digits_of(9**8 + 3**5 - 2, 3), 3) -- обратимость",
         core.value_of(core.digits_of(9 ** 8 + 3 ** 5 - 2, 3), 3)
         == 9 ** 8 + 3 ** 5 - 2)
    case("length_of(255, 2) == 8", core.length_of(255, 2) == 8)
    case("length_of(0, 36) == 1", core.length_of(0, 36) == 1)
    case("count_digit(8**10, 2, 1) == 1", core.count_digit(8 ** 10, 2, 1) == 1)
    case("sum_digits(255, 16) == 30", core.sum_digits(255, 16) == 30)
    case("sum_digits(int('4444', 5), 5, exclude=4) == 0",
         core.sum_digits(int("4444", 5), 5, exclude=4) == 0)
    case("count_distinct_digits(255, 16) == 1",
         core.count_distinct_digits(255, 16) == 1)
    case("digit_frequencies(int('1121', 5), 5) -> {1: 3, 2: 1}",
         core.digit_frequencies(int("1121", 5), 5) == {1: 3, 2: 1})
    case("max_digit(int('12012', 7), 7) == 2",
         core.max_digit(int("12012", 7), 7) == 2)
    case("first_digit(int('1230', 4), 4) == 1",
         core.first_digit(int("1230", 4), 4) == 1)
    case("position_from_right(255, 16, 15) == 0",
         core.position_from_right(255, 16, 15) == 0)
    case("position_from_right(int('1220', 4), 4, 2) == 1",
         core.position_from_right(int("1220", 4), 4, 2) == 1)
    case("position_from_right(255, 16, 1) is None",
         core.position_from_right(255, 16, 1) is None)
    case("count_pairs(int('66466', 7), 7, 6, 6) == 2",
         core.count_pairs(int("66466", 7), 7, 6, 6) == 2)
    case("count_pairs(int('61234', 7), 7, 6, (1, 5)) == 1",
         core.count_pairs(int("61234", 7), 7, 6, (1, 5)) == 1)
    case("truncate_low([1, 2, 3, 4], 3) -> [4]",
         core.truncate_low([1, 2, 3, 4], 3) == [4])
    case("truncate_low([0, 5], 5) -> [0]",
         core.truncate_low([0, 5], 5) == [0])
    case("replace_digit([7, 0, 7], 7, 0) -> [0, 0, 0]",
         core.replace_digit([7, 0, 7], 7, 0) == [0, 0, 0])
    case("zeros_to_max([0, 3, 0]) -> [3, 3, 3]",
         core.zeros_to_max([0, 3, 0]) == [3, 3, 3])
    case("is_prime: 1/0/9 ложь, 2/17 истина",
         not core.is_prime(1) and not core.is_prime(0)
         and not core.is_prime(9) and core.is_prime(2) and core.is_prime(17))

    # --- обработка ошибок -------------------------------------------------
    case("check_value(-1) -> NumsysError",
         _raises(CORE.NumsysError, core.check_value, -1))
    case("check_base(1) -> NumsysError",
         _raises(CORE.NumsysError, core.check_base, 1))
    case("check_digit(7, 7) -> NumsysError",
         _raises(CORE.NumsysError, core.check_digit, 7, 7))
    case("to_base_string(255, 121) -> NumsysError (основание > 36)",
         _raises(CORE.NumsysError, core.to_base_string, 255, 121))
    case("check_budget(2**20000) -> GenerationError",
         _raises(CORE.GenerationError, core.check_budget, 2 ** 20000))
    case("check_budget(2**19999) пропускает",
         core.check_budget(2 ** 19999) == 2 ** 19999)

    def exhausted():
        for _ in core.attempts(max_tries=3, what="тест"):
            continue

    case("attempts(3) без break -> GenerationError",
         _raises(CORE.GenerationError, exhausted))

    def short_circuit():
        for _ in core.attempts(max_tries=3, what="тест"):
            return True
        return False

    case("attempts(3) с break -> True", short_circuit() is True)

    # --- 300 случайных сверок с независимой реализацией -------------------
    generator = random.Random(20261105)
    mismatch = []
    for _ in range(300):
        base = generator.randint(2, 36)
        value = generator.randint(0, base ** generator.randint(1, 25))
        expected = reference_digits(value, base)
        digits = core.digits_of(value, base)
        checks = (
            "".join(core.DIGIT_CHARS[digit] for digit in reversed(digits))
            == expected,
            core.to_base_string(value, base, upper=False) == expected,
            core.value_of(digits, base) == value,
            core.length_of(value, base) == len(expected),
            core.sum_digits(value, base) == sum(int(ch, 36) for ch in expected),
            core.count_distinct_digits(value, base) == len(set(expected)),
            core.first_digit(value, base) == int(expected[0], 36),
            core.last_digit(value, base) == int(expected[-1], 36),
            core.max_digit(value, base) == max(int(ch, 36) for ch in expected),
        )
        if not all(checks):
            mismatch.append((value, base, expected, checks))
    case("300 случайных сверок (расхождений: %d)" % len(mismatch), not mismatch)

    return cases


def run(cases, title):
    """Печатает таблицу проверок и возвращает число падений."""
    failures = 0
    print("\n=== %s ===" % title)
    for description, passed in cases:
        status = "ok  " if passed else "FAIL"
        print("  [%s] %s" % (status, description))
        if not passed:
            failures += 1
    print("  --- всего: %d, провалено: %d" % (len(cases), failures))
    return failures


def main():
    """Запускает все доступные блоки самопроверки."""
    started = time.time()
    failures = run(core_cases(), "numsys_core")
    print("\nИтого провалов: %d, время: %.3f с" % (failures, time.time() - started))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
