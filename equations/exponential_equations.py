import re as r
import numpy as np
from sympy import *


def equation_determined(equation_string: str) -> (str, str):
    """
    Функция разбирает строку на константы, случайным образом присваивает им значения,
    пока не получится решаемое уравнение. Возвращает уравнение и его решение.
    """
    constants = r.findall(pattern=r'C\d', string=equation_string)
    while True:
        const_values = np.random.randint(1, 35, size=len(constants))
        if 0 in const_values:
            continue

        x = symbols('x')
        equation_string_with_digits = equation_string
        for i in range(len(constants)):
            equation_string_with_digits = r.sub(
                pattern=fr'{constants[i]}',
                repl=str(const_values[i]),
                string=equation_string_with_digits)

        parts = equation_string_with_digits.strip().split("=")
        equation = Eq(sympify(parts[0]), sympify(parts[1]))
        solution = solve(equation, x)

        if solution[0].is_real and not solution[0].is_irrational:

            task = 'Решите уравнение: $' + latex(equation) + '$'

            answer = ', '.join([str(solution[i]) for i in range(len(solution))])

            return task, answer


def simple_exponential_equation():
    """
    Простое показательное уравнение
    """
    equation_string = 'C1**(x+С2)=С3**С4'
    task, answer = equation_determined(equation_string)
    return {
        "condition": task,
        "answer": answer
    }


def exponential_equation_3665():
    """
    ID 3665
    показательное уравнение
    """
    equation_string = '(1/2)**(x-1)=(1/2)**2'
    task, answer = equation_determined(equation_string)
    return {
      "condition": task,
      "answer": answer
    }


if __name__ == "__main__":
    print(exponential_equation_3665())
