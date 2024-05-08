import re as r
import numpy as np
from sympy import *


def equation_determined(equation_string: str) -> Tuple(str, str):
    """
    Функция разбирает строку на константы, случайным образом присваивает им значения,
    пока не получится решаемое уравнение. Возвращает уравнение и его решение.
    """
    constants = r.findall(pattern=r'C\d', string=equation_string)
    while True:
        const_values = np.random.randint(-15, 40, size=len(constants))
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


def simple_quadratic_equation():
    """
    Простое квадратное уравнение
    """
    equation_string = 'C1*x**2+C2*x+C3=0'
    task, answer = equation_determined(equation_string)
    return task, answer


def quadratic_equation_2199():
    """
    ID 2199
    Квадратное уравнение
    """
    equation_string = '(C1*x+C2)*(C3*x+C4)=(C5*x+C6)**2'
    task, answer = equation_determined(equation_string)
    return task, answer


def quadratic_equation_2201():
    """
    ID 2201
    Квадратное уравнение
    """
    equation_string = '(C1*x+C2)**2+(C3*x+C4)*(C5*x+C6)=0'
    task, answer = equation_determined(equation_string)
    return task, answer


def quadratic_equation_2203():
    """
    ID 2203
    Квадратное уравнение
    """
    equation_string = '(C1*x+C2)/(C3*x+C4)=(C5*x+C6)/(C7*x+C8)'
    task, answer = equation_determined(equation_string)
    return task, answer


def quadratic_equation_2206():
    """
    ID 2206
    Квадратное уравнение
    """
    equation_string = '(C1*x+C2)/(C3*x+C4)+(C5*x+C6)/(C7*x+C8)=C9'
    task, answer = equation_determined(equation_string)
    return task, answer


def quadratic_equation_2259():
    """
    ID 2259
    Квадратное уравнение
    """
    equation_string = 'C1*x*(C2*x+C3)=C4*x+C5'
    task, answer = equation_determined(equation_string)
    return task, answer


def quadratic_equation_2287():
    """
    ID 2287
    Квадратное уравнение
    """
    equation_string = '(C1*x+C2)**2+C3*x*(C4*x+C5)=C6'
    task, answer = equation_determined(equation_string)
    return task, answer


def quadratic_equation_2264():
    """
    ID 2264
    Квадратное уравнение
    """
    equation_string = '(C1*x+C2)*(C3*x+C4)+C5=C6*x*(C7+C8*x)'
    task, answer = equation_determined(equation_string)
    return task, answer


def quadratic_equation_2266():
    """
    ID 2266
    Квадратное уравнение
    """
    equation_string = '(C1*x+C2)*(C3*x+C4)=C5*x*(C6*x+C7)'
    task, answer = equation_determined(equation_string)
    return task, answer


def quadratic_equation_2295():
    """
    ID 2295
    Квадратное уравнение
    """
    equation_string = '((C1*x**2+C2)/C3)-C4*x=C5'
    task, answer = equation_determined(equation_string)
    return task, answer


def quadratic_equation_2317():
    """
    ID 2317
    Квадратное уравнение
    """
    equation_string = 'C1*x+C2/x=C3'
    task, answer = equation_determined(equation_string)
    return task, answer


def quadratic_equation_2320():
    """
    ID 2320
    Квадратное уравнение
    """
    equation_string = '(C1*x**2+C2)/(C3*x**2+C4)=C5'
    task, answer = equation_determined(equation_string)
    return task, answer


def quadratic_equation_2333():
    """
    ID 2333
    Квадратное уравнение
    """
    equation_string = '(C1*x+C2)**2+C3*(C4*x+C5)**2=0'
    task, answer = equation_determined(equation_string)
    return task, answer


def quadratic_equation_6036():
    """
    ID 6036
    Квадратное уравнение
    """
    equation_string = '(C1*x**2+C2*x)/C3+C4*(C5*x**2+C6*x)/C7=0'
    task, answer = equation_determined(equation_string)
    return task, answer


def quadratic_equation_6159():
    """
    ID 6159
    Квадратное уравнение
    """
    equation_string = '(C1*x+C2)*(C3*x+C4)+C5*x*(C6*x+C7)=C8*x*(C9*x+C10)'
    task, answer = equation_determined(equation_string)
    return task, answer


def quadratic_equation_6169():
    """
    ID 6169
    Квадратное уравнение
    """
    equation_string = '(C1*x**2+C2*x)/C3=(C4*x+C5)/C6'
    task, answer = equation_determined(equation_string)
    return task, answer


def quadratic_equation_6170():
    """
    ID 6170
    Квадратное уравнение
    """
    equation_string = '(C1*x**2+C2*x)/C3+(C4*x+C5)/C6=(C7*x**2+C8)/C9'
    task, answer = equation_determined(equation_string)
    return task, answer


def quadratic_equation_6207():
    """
    ID 6207
    Квадратное уравнение
    """
    equation_string = '(C1*x**2+C2*x+C3)**2=(C4*x**2+C5*x+C6)**2'
    task, answer = equation_determined(equation_string)
    return task, answer


def quadratic_equation_12456():
    """
    ID 12456
    Квадратное уравнение
    """
    equation_string = '(C1*x+C2)*(C3*x+C4)+C5*x*(C6+C7*x)=C8'
    task, answer = equation_determined(equation_string)
    return task, answer


def quadratic_equation_12457():
    """
    ID 12457
    Квадратное уравнение
    """
    equation_string = '(C1*x+C2)**2+C3=C4+C5*x**2'
    task, answer = equation_determined(equation_string)
    return task, answer
