from sympy import *
import numpy as np
import fractions
from fractions import Fraction
import random
import math
import decimal

def task_1554():
    '''Задача №1554 с портала https://kuzovkin.info/one_exercise_1/1554 '''
    while True:
      a, b = np.random.randint(2, 20, size=2)
      m = np.random.randint(2, 5)
      n = 2*m
      x, y = symbols('x y')
      task = r'Найдите значение алгебраической дроби: \( \frac{'+latex(pow(UnevaluatedExpr(x), m))+('+')+latex(pow(y, m))+'}{'+latex(pow(UnevaluatedExpr(x), n))+('-')+latex(pow(y, n))+'} \) при \(' +latex(x)+str('=')+latex(UnevaluatedExpr(a))+str(',')+latex(y)+str('=')+latex(UnevaluatedExpr(b))+ '\)'
      answer = 1/(pow(a, 2)-pow(b, 2))
      if a>b:
        if abs(answer*1000 - int(answer*1000)) < 0.000001:
          break
    return {
      "condition": task,
      "answer": answer
    }

def task_1555():
    '''Задача №1555 с портала https://kuzovkin.info/one_exercise_1/1555 '''
    while True:
      a, b = np.random.randint(-5, 10, size=2)
      m, n = symbols('m n')
      task = r'Найдите значение алгебраической дроби: \( \frac{'+latex(pow(m, 4))+('-')+latex(pow(n, 4))+'}{'+latex(pow(m, 3)*n)+('-')+latex(m*pow(n, 3))+'} \) при \(' +latex(m)+str('=')+latex(UnevaluatedExpr(a))+str(',')+latex(n)+str('=')+latex(UnevaluatedExpr(b))+ '\)'
      answer = (pow(a, 2)+pow(b, 2))/(a*b)
      if a>b and a*b!=0:
        if abs(answer*1000 - int(answer*1000)) < 0.000001:
          break
    return {
      "condition": task,
      "answer": answer
    }

def task_1581():
    '''Задача №1581 с портала https://kuzovkin.info/one_exercise_1/1581 '''
    while True:
      k = np.random.randint(2, 10)
      a, b = symbols('a b')
      task = r'Зная, что \( \frac{'+latex(a)+'}{'+latex(b)+'} {'+str('=')+latex(UnevaluatedExpr(k))+'} \), найдите значение выражения: \( \\frac{'+latex(b)+'}{'+latex(a)+'} \)'
      answer = r'\frac{'+latex(UnevaluatedExpr(1))+'}{'+latex(UnevaluatedExpr(k))+'}'
      if k:
        break
    return {
      "condition": task,
      "answer": answer
    }

def task_1583():
    '''Задача №1583 с портала https://kuzovkin.info/one_exercise_1/1583 и аналогичная 1'''
    while True:
      k = np.random.randint(2, 10)
      a, b = symbols('a b')
      task = r'Зная, что \( \frac{'+latex(a)+'}{'+latex(b)+'} {'+str('=')+latex(UnevaluatedExpr(k))+'} \), найдите значение выражения: \( \\frac{'+latex(b+UnevaluatedExpr(2*a))+'}{'+latex(a)+'} \)'
      whole_path = 2
      answer = r'\( {'+latex(UnevaluatedExpr(whole_path))+'} \\frac{'+latex(UnevaluatedExpr(1))+'}{'+latex(UnevaluatedExpr(k))+'} \)'
      if k:
        break
    return {
      "condition": task,
      "answer": answer
    }

def task_1584():
    '''Задача №1584 с портала https://kuzovkin.info/one_exercise_1/1584 '''
    while True:
      a, b = np.random.randint(2, 10, size=2)
      x, y = symbols('x y')
      task = r'Зная, что \( \frac{'+latex(x)+'}{'+latex(y)+'} {'+str('=')+'} \\frac{'+latex(UnevaluatedExpr(a))+'}{'+latex(UnevaluatedExpr(b))+'} \), найдите значение выражения: \( \\frac{'+latex(x)+'}{'+latex(2*y)+'} \)'
      result = fractions.Fraction(a, 2*b)
      answer = Fraction(result).limit_denominator()
      if a<b and a%b!=0:
        break
    return {
      "condition": task,
      "answer": answer
    }

def task_1588():
    '''Задача №1588 с портала https://kuzovkin.info/one_exercise_1/1588 '''
    while True:
      k = np.random.randint(1, 26)/10
      x, y = symbols('x y')
      task = r'Надйите значение дроби \( \frac{'+latex(x+y)+'}{'+latex(x)+'} \), если \( \\frac{'+latex(x)+'}{'+latex(y)+'}{'+str('=')+'}{'+latex(UnevaluatedExpr(k))+'} \)'
      answer = int(1+pow(k, -1))
      if pow(k, -1)==int(pow(k, -1)):
        break
    return {
      "condition": task,
      "answer": answer
    }

def task_1591():
    '''Задача №1591 с портала https://kuzovkin.info/one_exercise_1/1591 '''
    while True:
      k = np.random.randint(2, 20)
      a, b = symbols('a b')
      task = r'Зная, что \( \frac{'+latex(a+UnevaluatedExpr(2*b))+'}{'+latex(b)+'} {'+str('=')+'} {'+latex(UnevaluatedExpr(k))+'} \), найдите значение выражения: \( \\frac{'+latex(2*a-b)+'}{'+latex(2*b)+'} \)'
      answer = k-2.5
      if k:
        break
    return {
      "condition": task,
      "answer": answer
    }

def task_1596():
    '''Задача №1596 с портала https://kuzovkin.info/one_exercise_1/1596 '''
    while True:
      k = np.random.randint(2, 20)
      x, y = symbols('x y')
      task = r'Зная, что \( \frac{'+latex(x-UnevaluatedExpr(3*y))+'}{'+latex(y)+'} {'+str('=')+'} {'+latex(UnevaluatedExpr(k))+'} \), найдите значение выражения: \( \\frac{'+latex(y)+'}{'+latex(x)+'} \)'
      result = fractions.Fraction(1, k+3)
      answer = Fraction(result).limit_denominator()
      if k:
        break
    return {
      "condition": task,
      "answer": answer
    }

def task_1785():
    '''Задача №1785 с портала https://kuzovkin.info/one_exercise_1/1785 '''
    while True:
      a, b, c, d = np.random.randint(1, 10, size=4)
      k = np.random.randint(2, 40)/10
      x = symbols('x')
      task = r'Упростите выражение и найдите его значение: \( \frac{'+latex(UnevaluatedExpr(c))+('+')+latex(UnevaluatedExpr(a*x))+'}{'+latex((UnevaluatedExpr(a)+x)*(UnevaluatedExpr(b)-UnevaluatedExpr(x)))+'} {'+str('+')+'} \\frac{'+latex(UnevaluatedExpr(d)+x)+'}{'+latex((x+UnevaluatedExpr(a))*(x-UnevaluatedExpr(b)))+'}\) при \(' +latex(UnevaluatedExpr(x))+str('=')+latex(UnevaluatedExpr(k))+ '\)'
      answer = 1/(b-k)
      if a!=b and b!=k:
        if abs(answer*1000 - int(answer*1000)) < 0.000001:
          break
    return {
      "condition": task,
      "answer": round(answer, 5)
    }

def task_1883():
    '''Задача №1883 с портала https://kuzovkin.info/one_exercise_1/1883'''
    while True:
      a, b, m, n, f, h = np.random.randint(2, 10, size=6)
      c = symbols('c')
      check = b*h-a*f
      task = r'Упростите выражение: \( \frac{'+latex(c)+('-')+latex(UnevaluatedExpr(b))+'}{'+latex(UnevaluatedExpr(b*m*c))+('+')+latex(UnevaluatedExpr(b*n))+'} {'+str('-')+'} \\frac{'+latex(UnevaluatedExpr(c))+('-')+latex(UnevaluatedExpr(h))+'}{'+latex(UnevaluatedExpr(a*m*c))+('+')+latex(UnevaluatedExpr(a*n))+'} \)'
      answer = 1/(a*b)
      if check == n:
        if abs(answer*1000 - int(answer*1000)) < 0.000001:
          break
    return {
      "condition": task,
      "answer": round(answer, 5)
    }

def task_1947():
    '''Задача №1947 с портала https://kuzovkin.info/one_exercise_1/1947 '''
    while True:
      a, b, n, k = np.random.randint(1, 25, size=4)
      c, d = symbols('c d')
      task = r'Упростите выражение: \( \frac{'+latex(UnevaluatedExpr(b*c))+'}{'+latex(UnevaluatedExpr(a*d))+'} {'+str(':')+'} ( {'+str('-')+'} \\frac{'+latex(UnevaluatedExpr(k*c))+'}{'+latex(UnevaluatedExpr(n*d))+'}) \)'
      answer = -(b*n)*(k*a)
      if k%b==0 and a%n==0:
        if abs(answer*1000 - int(answer*1000)) < 0.000001 and answer<=1000 and answer>=-1000:
          break
    return {
      "condition": task,
      "answer": answer
    }

def task_1967():
    '''Задача №1967 с портала https://kuzovkin.info/one_exercise_1/1967 '''
    while True:
      a, b, n, k = np.random.randint(8, 100, size=4)
      c, r, s = symbols('c r s')
      task = r'Упростите выражение: \( \frac{'+latex(UnevaluatedExpr(a*r))+('-')+latex(UnevaluatedExpr(b*s))+'}{'+latex(UnevaluatedExpr(k*c))+'} {'+str('\cdot')+'} \\frac{'+latex(UnevaluatedExpr(n*c))+'}{'+latex(UnevaluatedExpr(b*s))+('-')+latex(UnevaluatedExpr(a*r))+'} \)'
      answer = -(n/k)
      if n%k==0 and n!=k and a!=b:
        break
    return {
      "condition": task,
      "answer": int(answer)
    }

def task_5492():
    '''Задача №5492 с портала https://kuzovkin.info/one_exercise_1/5492 '''
    while True:
      m, n, k, c = np.random.randint(1, 10, size=4)
      f = np.random.randint(1, 7)/10
      a, b = symbols('a b')
      task = r'Найдите значение дроби: \( \frac{'+latex(UnevaluatedExpr(k*c*a))+('+')+latex(UnevaluatedExpr(k*n*b))+'}{'+latex(UnevaluatedExpr(f*pow(c, 2))*UnevaluatedExpr(pow(a, 2)))+('-')+latex(UnevaluatedExpr(f*pow(n, 2))*UnevaluatedExpr(pow(b, 2)))+'} \), если \(' +latex(a-2*b)+str('=')+latex(UnevaluatedExpr(m))+str(',')+latex(a+2*b)+str('\u2260')+latex(UnevaluatedExpr(0))+ '\)'
      answer = k/(f*m)
      check = k%f
      if c!=n and f*pow(c, 2)!=int(f*pow(c, 2)) and f*pow(n, 2)!=int(f*pow(n, 2)):
        if check==int(check) and answer!=0:
          break
    return {
      "condition": task,
      "answer": int(answer)
    }

def task_5493():
    '''Задача №5493 с портала https://kuzovkin.info/one_exercise_1/5493 '''
    while True:
      a, b, m, n = np.random.randint(1, 10, size=4)
      c = np.random.randint(1, 10)/10
      d = np.random.randint(1, 100)/100
      x, y = symbols('x y')
      task = r'Найдите значение дроби: \( \frac{'+latex(UnevaluatedExpr(a*m*pow(x, 2)))+('-')+latex(UnevaluatedExpr(a*n*x*y))+'}{'+latex(UnevaluatedExpr(b*m*x*y))+('-')+latex(UnevaluatedExpr(b*n*pow(y, 2)))+'} \) при \(' +latex(x)+str('=')+latex(UnevaluatedExpr(c))+str(',')+latex(y)+str('=')+latex(UnevaluatedExpr(d))+ '\)'
      answer = (a*c)/(b*d)
      if a!=b and m!=n:
        if abs(answer*1000 - int(answer*1000)) < 0.000001:
          break
    return {
      "condition": task,
      "answer": answer
    }

def task_5494():
    '''Задача №5494 с портала https://kuzovkin.info/one_exercise_1/5494 '''
    while True:
      m, n, k, f = np.random.randint(1, 7, size=4)
      x = -np.random.randint(11, 30)/10
      y = np.random.randint(1, 10)/10
      a, b = symbols('a b')
      task = r'Найдите значение дроби: \( \frac{'+latex(UnevaluatedExpr(f*pow(m, 2))*UnevaluatedExpr(pow(a, 3)))+('-')+latex(UnevaluatedExpr(f*pow(n, 2)*a*pow(b, 2)))+'}{'+latex(UnevaluatedExpr(k*n*pow(b, 2)))+('-')+latex(UnevaluatedExpr(k*m*a*b))+'} \), при \(' +latex(a)+str('=')+latex(UnevaluatedExpr(x))+str(',')+latex(b)+str('=')+latex(UnevaluatedExpr(y))+ '\)'
      answer = -(x*f*(m*x+n*y))/(k*y)
      if m!=n and k!=f:
        if abs(answer*1000 - int(answer*1000)) < 0.000001:
          break
    return {
      "condition": task,
      "answer": int(answer)
    }

def task_5475():
    '''Задача №5475 с портала https://kuzovkin.info/one_exercise_1/5475 '''
    while True:
      a, b, c, m, n, k = np.random.randint(2, 10, size=6)
      x, y = symbols('x y')
      task = r'Пусть \( \frac{'+latex(x)+'}{'+latex(y)+'}{'+str('=')+'}{'+latex(UnevaluatedExpr(k))+'} \). Найдите значение дроби: \( \\frac{'+latex(UnevaluatedExpr(a)*UnevaluatedExpr(pow(x, 2)))+('-')+latex(UnevaluatedExpr(b)*UnevaluatedExpr(x*y))+('+')+latex(UnevaluatedExpr(c)*UnevaluatedExpr(pow(y, 2)))+'}{'+latex(UnevaluatedExpr(m)*UnevaluatedExpr(pow(x, 2)))+('+')+latex(UnevaluatedExpr(n)*UnevaluatedExpr(pow(y, 2)))+'} \)'
      num = a*pow(k, 2)-b*k+c
      den = m*pow(k, 2)+n
      answer = num/den
      if a!=b!=k and m!=n!=k:
        if answer==int(answer) and answer!=0:
          break
    return {
      "condition": task,
      "answer": int(answer)
    }

def task_5459():
    '''Задача №5459 с портала https://kuzovkin.info/one_exercise_1/5459 '''
    while True:
      k, n, m = np.random.randint(1, 15, size=3)
      x, y = symbols('x y')
      task = r'Зная, что \( \frac{'+latex(x)+'}{'+latex(y)+'} {'+str('=')+'} \\frac{'+latex(UnevaluatedExpr(k))+'}{'+latex(UnevaluatedExpr(n))+'} \), найдите значение выражения: \( \\frac{'+latex(y)+'}{'+latex(UnevaluatedExpr(m)*UnevaluatedExpr(x))+'} \)'
      answer = n/(m*k)
      if k<n and m!=1 and n%k!=0:
        if abs(answer*1000 - int(answer*1000)) < 0.000001:
          break
    return {
      "condition": task,
      "answer": answer
    }

def task_5460():
    '''Задача №5460 с портала https://kuzovkin.info/one_exercise_1/5460 '''
    while True:
      k, n = np.random.randint(1, 15, size=2)
      x, y = symbols('x y')
      task = r'Зная, что \( \frac{'+latex(x)+'}{'+latex(y)+'} {'+str('=')+'} \\frac{'+latex(UnevaluatedExpr(k))+'}{'+latex(UnevaluatedExpr(n))+'} \), найдите значение выражения: \( \\frac{'+latex(x-y)+'}{'+latex(y)+'} \)'
      answer = k/n-1
      if k<n:
        if abs(answer*1000 - int(answer*1000)) < 0.000001:
          break
    return {
      "condition": task,
      "answer": round(answer, 5)
    }

def task_5462():
    '''Задача №5462 с портала https://kuzovkin.info/one_exercise_1/5462 '''
    while True:
      a, b = np.random.randint(2, 10, size=2)
      k = np.random.randint(1, 10)/10
      x, y = symbols('x y')
      task = r'Найдите значение дроби: \( \frac{'+latex(UnevaluatedExpr(a)*UnevaluatedExpr(x))+('-')+latex(UnevaluatedExpr(b)*UnevaluatedExpr(y))+'}{'+latex(y)+'}\), если \( \\frac{'+latex(x)+'}{'+latex(y)+'}{'+str('=')+'}{'+latex(UnevaluatedExpr(k))+'} \)'
      answer = a*k-b
      if a!=b:
        if abs(answer*1000 - int(answer*1000)) < 0.000001 or answer==int(answer):
          break
    return {
      "condition": task,
      "answer": round(answer, 5)
    }

def task_5465():
    '''Задача №5465 с портала https://kuzovkin.info/one_exercise_1/5465 '''
    while True:
      k, m, c, d = np.random.randint(2, 10, size=4)
      a, b = symbols('a b')
      task = r'Зная, что \( \frac{'+latex(a)+('+')+latex(UnevaluatedExpr(m*b))+'}{'+latex(b)+'} {'+str('=')+'} {'+latex(UnevaluatedExpr(k))+'} \), найдите значение выражения: \( \\frac{'+latex(UnevaluatedExpr(c*a))+('+')+latex(UnevaluatedExpr(d*b))+'}{'+latex(b)+'} \)'
      answer = c*(k-m)+d
      if k!=m and c!=d:
        if answer!=0:
          break
    return {
      "condition": task,
      "answer": answer
    }

def task_5449():
    '''Задача №5449 с портала https://kuzovkin.info/one_exercise_1/5449 '''
    while True:
      a, b, m, k = np.random.randint(1, 10, size=4)
      x, y = symbols('x y')
      task = r'Зная, что \( {'+latex(UnevaluatedExpr(k*a*x))+('-')+latex(UnevaluatedExpr(k*b*y))+'} {'+str('=')+'} {'+latex(UnevaluatedExpr(m))+'} \), найдите значение выражения: \( {'+latex(UnevaluatedExpr(a*x))+('-')+latex(UnevaluatedExpr(b*y))+'} \)'
      answer = m/k
      if m%k==0 or abs(answer*1000 - int(answer*1000)) < 0.000001:
        if a!=b and k!=m:
          break
    return {
      "condition": task,
      "answer": answer
    }

def task_5450():
    '''Задача №5450 с портала https://kuzovkin.info/one_exercise_1/5450 и аналогичная 5451 '''
    while True:
      a, b, m, k, f = np.random.randint(1, 10, size=5)
      x, y = symbols('x y')
      task = r'Зная, что \( {'+latex(UnevaluatedExpr(k*a*x))+('-')+latex(UnevaluatedExpr(k*b*y))+'} {'+str('=')+'} {'+latex(UnevaluatedExpr(m))+'} \), найдите значение выражения: \( \\frac{'+latex(UnevaluatedExpr(f))+'}{'+latex(UnevaluatedExpr(a*x))+('-')+latex(UnevaluatedExpr(b*y))+'} \)'
      answer = (f*k)/m
      if abs(answer*1000 - int(answer*1000)) < 0.000001 or answer==int(answer):
        if a!=b and k!=m:
          break
    return {
      "condition": task,
      "answer": answer
    }

def task_5452():
    '''Задача №5452 с портала https://kuzovkin.info/one_exercise_1/5452 '''
    while True:
      a, b, m, k, f = np.random.randint(1, 8, size=5)
      x, y = symbols('x y')
      task = r'Зная, что \( {'+latex(UnevaluatedExpr(k*a*x))+('-')+latex(UnevaluatedExpr(k*b*y))+'} {'+str('=')+'} {'+latex(UnevaluatedExpr(m))+'} \), найдите значение выражения: \( ({'+latex(UnevaluatedExpr(pow(b, 2)*pow(y, 2)))+('-')+latex(UnevaluatedExpr(2*a*b*x*y))+('+')+latex(UnevaluatedExpr(pow(a, 2)*pow(b, 2)))+'}){'+str('\cdot')+'}{'+latex(UnevaluatedExpr(f))+'} \)'
      answer = pow(m/k, 2)*f
      if m%k==0 or abs(answer*1000 - int(answer*1000)) < 0.000001:
        if a!=b and k!=m:
          break
    return {
      "condition": task,
      "answer": answer
    }

def task_5496():
    '''Задача №5496 с портала https://kuzovkin.info/one_exercise_1/5496 '''
    while True:
      a, b, c, d, m, n = np.random.randint(2, 10, size=6)
      k, l = symbols('k l')
      task = r'Найдите значение дроби: \( \frac{'+latex(UnevaluatedExpr(m*a)*UnevaluatedExpr(k*l))+('-')+latex(UnevaluatedExpr(m*b)*UnevaluatedExpr(pow(k, 2)))+'}{'+latex(UnevaluatedExpr(n*b)*UnevaluatedExpr(k*l))+('-')+latex(UnevaluatedExpr(n*a)*UnevaluatedExpr(pow(l, 2)))+'}\), при \( {'+latex(k)+'}{'+str('=')+'}\\frac{'+latex(UnevaluatedExpr(1))+'}{'+latex(UnevaluatedExpr(c))+'}{'+str(';')+'}{'+latex(l)+'}{'+str('=')+'}\\frac{'+latex(UnevaluatedExpr(1))+'}{'+latex(UnevaluatedExpr(d))+'} \)'
      answer = -(m*d)/(c*n)
      if a!=b and m%c==0 and n%d==0:
        if abs(answer*1000 - int(answer*1000)) < 0.000001 or answer==int(answer):
          break
    return {
      "condition": task,
      "answer": answer
    }

def task_5838():
    '''Задача №5838 с портала https://kuzovkin.info/one_exercise_1/5838 '''
    while True:
      a, b, k = np.random.randint(2, 10, size=3)
      m, n, c = symbols('m n c')
      task = r'Упростите выражение: \( \frac{'+latex(UnevaluatedExpr(a*m))+('-')+latex(n)+'}{'+latex(UnevaluatedExpr(b*c))+'} {'+str('\cdot')+'} \\frac{'+latex(UnevaluatedExpr(k*c))+'}{'+latex(n)+('-')+latex(UnevaluatedExpr(a*m))+'} \)'
      answer = r'\( -\frac{'+latex(UnevaluatedExpr(k))+'}{'+latex(UnevaluatedExpr(b))+'} \)'
      if k<b:
        break
    return {
      "condition": task,
      "answer": answer
    }


def task_5853():
    '''Задача №5853 с портала https://kuzovkin.info/one_exercise_1/5853 '''
    while True:
      a, b, k = np.random.randint(2, 10, size=3)
      x, y, p = symbols('x y p')
      task = r'Упростите выражение: \( \frac{'+latex(UnevaluatedExpr(a*p))+('-')+latex(pow(p, 2))+'}{'+latex(y)+('-')+latex(x)+'} {'+str(':')+'} \\frac{'+latex(UnevaluatedExpr(a*k*p))+('-')+latex(UnevaluatedExpr(b*k*pow(p, 2)))+'}{'+latex(x-y)+'} \)'
      answer = -1/k
      if abs(answer*1000 - int(answer*1000)) < 0.000001 or answer==int(answer):
        if a!=b:
          break
    return {
      "condition": task,
      "answer": answer
    }


def task_5854():
    '''Задача №5854 с портала https://kuzovkin.info/one_exercise_1/5854 '''
    while True:
      x, y, k = np.random.randint(2, 10, size=3)
      a, b, q = symbols('a b q')
      task = r'Упростите выражение: \( \frac{'+latex(a)+('-')+latex(b)+'}{'+latex(UnevaluatedExpr(x*q))+('-')+latex(pow(q, 2))+'} {'+str('\cdot')+'} \\frac{'+latex(UnevaluatedExpr(k*x*q))+('-')+latex(UnevaluatedExpr(k*y*pow(q, 2)))+'}{'+latex(b)+('-')+latex(a)+'} \)'
      answer = -k
      if x!=y:
        break
    return {
      "condition": task,
      "answer": answer
    }


def task_11915():
    '''Задача №11915 с портала https://kuzovkin.info/one_exercise_1/11915 '''
    while True:
      a, b, k = np.random.randint(1, 10, size=3)
      p = symbols('p')
      task = r'Выполните сложение алгебраических дробей: \( \frac{'+latex(UnevaluatedExpr(k*a))+'}{'+latex(UnevaluatedExpr(a))+('+')+latex(UnevaluatedExpr(b*p))+'} {'+str('+')+'} \\frac{'+latex(UnevaluatedExpr(k*b*p))+'}{'+latex(UnevaluatedExpr(a))+('+')+latex(UnevaluatedExpr(b*p))+'} \)'
      answer = k
      if k!=a!=b:
        break
    return {
      "condition": task,
      "answer": answer
    }


def task_11947():
    '''Задача №11947 с портала https://kuzovkin.info/one_exercise_1/11947 '''
    while True:
      a, x, y = np.random.randint(1, 10, size=3)
      m_ = np.random.randint(-50, 50)/10
      m = symbols('m')
      task = r'Упростите и найдите значение выражения: \( \frac{'+latex(UnevaluatedExpr(pow(m-x, 2)))+'}{'+latex(pow(m, 3))+('+')+latex(UnevaluatedExpr(pow(a, 3)))+'} {'+str('+')+'} \\frac{'+latex(UnevaluatedExpr(y))+('-')+latex(m)+'}{'+latex(pow(m, 3))+('+')+latex(UnevaluatedExpr(pow(a, 3)))+'} \), при \( {'+latex(m)+('=')+latex(UnevaluatedExpr(m_))+'} \)'
      answer = 1/(m_+a)
      check_1 = pow(x, 2)+y
      check_2 = 2*x-1
      if a!=x!=y and m_!=int(m_) and m_!=0:
        if check_1==pow(a, 2) and check_2==a:
          if abs(answer*1000 - int(answer*1000)) < 0.000001:
            break
    return {
      "condition": task,
      "answer": round(answer, 5)
    }


def task_11997():
    '''Задача №11997 с портала https://kuzovkin.info/one_exercise_1/11997 '''
    while True:
      a, b, k, n = np.random.randint(1, 10, size=4)
      c = 3*a
      x, y = symbols('x y')
      task = r'Упростите выражение и найдите его значение: \( \frac{'+latex(UnevaluatedExpr(c*x))+('+')+latex(UnevaluatedExpr(b*y))+'}{'+latex(UnevaluatedExpr(a*pow(x, 2)*y))+'} {'+str('-')+'} \\frac{'+latex(UnevaluatedExpr(b*y))+('-')+latex(UnevaluatedExpr(a*x))+'}{'+latex(UnevaluatedExpr(b*x*pow(y, 2)))+'} \), при \( {'+latex(x)+'}{'+str('=')+'}\\frac{'+latex(UnevaluatedExpr(1))+'}{'+latex(UnevaluatedExpr(k))+'}{'+str(';')+'}{'+latex(y)+'}{'+str('=')+'}\\frac{'+latex(UnevaluatedExpr(1))+'}{'+latex(UnevaluatedExpr(n))+'} \)'
      answer = (pow(a*(1/k+b*(1/n)) ,2))/(a*b*(pow(1/k, 2))*(pow(1/n, 2)))
      if abs(answer*1000 - int(answer*1000)) < 0.000001 and k!=1 and n!=1:
        if a!=x!=y and a%k==0 and b%n==0:
          break
    return {
      "condition": task,
      "answer": int(answer)
    }


def task_16072():
    '''Задача №16072 с портала https://kuzovkin.info/one_exercise_1/16072 '''
    while True:
      x, y, z = np.random.randint(2, 15, size=3)
      a, b, c = symbols('a b c')
      task = r'Упростите выражение и найдите его значение: \( ((\frac{'+latex(UnevaluatedExpr(1))+'}{'+latex(a)+'} {'+str('+')+'} \\frac{'+latex(UnevaluatedExpr(1))+'}{'+latex(b+c)+'}) {'+str(':')+'} (\\frac{'+latex(UnevaluatedExpr(1))+'}{'+latex(a)+'} {'+str('-')+'} \\frac{'+latex(UnevaluatedExpr(1))+'}{'+latex(b+c)+'})) {'+str(':')+'} ({'+latex(UnevaluatedExpr(1))+'}{'+str('+')+'} \\frac{'+latex(pow(b, 2))+('+')+latex(pow(c, 2))+('-')+latex(pow(a, 2))+'}{'+latex(2*b*c)+'}) \), при \( {'+latex(a)+'}{'+str('=')+'} {'+latex(UnevaluatedExpr(x))+'}{'+str(';')+'}{'+latex(b)+'}{'+str('=')+'}{'+latex(UnevaluatedExpr(y))+'}{'+str(';')+'}{'+latex(c)+'}{'+str('=')+'}{'+latex(UnevaluatedExpr(z))+'} \)'
      answer = (2*y*z)/pow(y+z-x, 2)
      if abs(answer*1000 - int(answer*1000)) < 0.000001 or abs(int(answer*1000) - answer*1000) < 0.000001:
        if x!=y!=z and pow(y+z-x, 2)!=0:
          break
    return {
      "condition": task,
      "answer": answer
    }

def task_16075():
    '''Задача №16075 с портала https://kuzovkin.info/one_exercise_1/16075 '''
    while True:
      a, b, c, d = np.random.randint(1, 15, size=4)
      x_ = np.random.randint(1, 15)/10
      x = symbols('x')
      task = r'Упростите выражение и найдите его значение: \( ({'+latex(pow(x, 2))+('+')+latex(UnevaluatedExpr(a*x))+('-')+'} \\frac{'+latex(UnevaluatedExpr(c*x))+('-')+latex(UnevaluatedExpr(a))+'}{'+latex(UnevaluatedExpr(b*x))+('+')+latex(UnevaluatedExpr(d))+'}) {'+str(':')+'} ({'+latex(x)+('+')+latex(UnevaluatedExpr(d))+('-')+'} \\frac{'+latex(UnevaluatedExpr(a*pow(x, 2)))+('+')+latex(x)+('+')+latex(UnevaluatedExpr(a))+'}{'+latex(UnevaluatedExpr(b*x))+('+')+latex(UnevaluatedExpr(d))+'}) \), при \( {'+latex(x)+'}{'+str('=')+'}{'+latex(UnevaluatedExpr(x_))+'} \)'
      answer = b*x_-a
      if abs(answer*1000 - int(answer*1000)) < 0.000001 or abs(int(answer*1000) - answer*1000) < 0.000001:
        if c>a and c>b and c>d:
          break
    return {
      "condition": task,
      "answer": round(answer, 5)
    }

def task_16080():
    '''Задача №16080 с портала https://kuzovkin.info/one_exercise_1/16080 '''
    while True:
      a, m, k = np.random.randint(2, 15, size=3)
      b = a+1
      c = b+1
      n = m+1
      f = 4*b
      t = symbols('t')
      task = r'Упростите выражение: \( {(\frac{'+latex(UnevaluatedExpr(1))+'}{'+latex(pow(t, 2))+('+')+latex(UnevaluatedExpr(b*t))+('+')+latex(UnevaluatedExpr(a))+'} {'+str('+')+'} \\frac{'+latex(UnevaluatedExpr(2*t))+'}{'+latex(pow(t, 2))+('+')+latex(UnevaluatedExpr(c*t))+('+')+latex(UnevaluatedExpr(b))+'} {'+str('+')+'} \\frac{'+latex(UnevaluatedExpr(1))+'}{'+latex(pow(t, 2))+('+')+latex(UnevaluatedExpr(m*t))+('+')+latex(UnevaluatedExpr(n))+'})}^{'+latex(UnevaluatedExpr(2))+'} {'+str('\cdot')+'} \\frac{'+latex(pow(UnevaluatedExpr(t-b), 2))+('+')+latex(UnevaluatedExpr(f*t))+'}{'+latex(UnevaluatedExpr(k))+'} \)'
      answer = k
      if a!=m and a<10:
        break
    return {
      "condition": task,
      "answer": answer
    }
