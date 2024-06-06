import random
import numpy as np
from fractions import Fraction
from text_tasks.utils import choosing_declension_form, generate_context, find_genus_object, capitalize_word


def task_2598():
    """Генерация аналогичных задач № 2598 с портала https://kuzovkin.info/one_exercise_1/2598
    Моторная лодка прошла 54 км по течению реки и 42 км против течения за то же время, что
    она проходит 96 км в стоячей воде. Найдите скорость лодки в стоячей воде, если
    скорость течения реки равна 3 км/ч."""
    vehicle = random.sample(generate_context('context.json', 'vehicle'), 1)[0]
    water_vel = random.randint(2, 8)
    boat_vel = random.randint(15, 45)
    time = random.randint(2, 5)
    s1 = (boat_vel + water_vel) * time
    s2 = (boat_vel - water_vel) * time
    s3 = boat_vel * time * 2
    task = (f'{capitalize_word(vehicle)} {"прошёл" if find_genus_object(vehicle) == 1 else "прошла"} {s1} '
            f'км по течению реки и {s2} км против течения за то же время, что '
            f'{"он" if find_genus_object(vehicle) == 1 else "она"} проходит {s3} км в стоячей воде. '
            f'Найдите скорость {choosing_declension_form(vehicle)} в стоячей воде, если'
            f' скорость течения реки равна {water_vel} км/ч.')
    return {
        "condition": task,
        "answer": boat_vel
    }


def task_2604():
    """Генерация аналогичных задач № 2604 с портала https://kuzovkin.info/one_exercise_1/2604
    Турист проплыл на байдарке 15 км против течения реки и 14 км по течению, затратив на все путешествие столько же
    времени, сколько ему понадобилось бы, чтобы проплыть по озеру 30 км. Зная, что скорость течения реки равна 1 км/ч,
    найдите скорость движения туриста по озеру."""
    actor = random.sample(generate_context('context.json', 'actor'), 1)[0]
    vehicle = random.sample(generate_context('context.json', 'vehicle'), 1)[0]
    water_vel = random.randint(1, 6)
    boat_vel = random.randint(water_vel+1, 15)
    time1 = random.randint(1, 3)
    time2 = random.randint(1, 3)
    s1 = (boat_vel + water_vel) * time1
    s2 = (boat_vel - water_vel) * time2
    s3 = boat_vel * (time1 + time2)
    task = (f'{capitalize_word(actor)} проплыл на {choosing_declension_form(vehicle, 'loct')} {s2} км против течения реки и '
            f'{s1} км по течению, затратив на все путешествие '
            f'столько же времени, сколько ему понадобилось бы, чтобы проплыть по озеру {s3} км. Зная, что скорость '
            f'течения реки равна {water_vel} км/ч, найдите скорость движения {choosing_declension_form(actor)} по озеру.')
    return {
        "condition": task,
        "answer": boat_vel
    }


def task_3888():
    """Генерация аналогичных задач № 3888 с портала https://kuzovkin.info/one_exercise_1/3888
    Плот проплывает путь от A до B за 40 ч, а катер – за 4 ч. За сколько часов проплывет катер путь от B до A ?"""
    # на 10000 проходов функции среднее количество циклов менее 25
    vehicle = random.sample(generate_context('context.json', 'vehicle'), 1)[0]
    raft = random.sample(generate_context('context.json', 'raft'), 1)[0]
    while True:
        raft_time = random.randint(20, 80)
        boat_time = random.randint(1, 8)
        result_fraction = Fraction(1, boat_time) - Fraction(2, raft_time)
        if result_fraction.numerator == 1:
            boat_time2 = result_fraction.denominator
            break
    task = (f'{capitalize_word(raft)} проплывает путь от A до B за {raft_time} ч, а {vehicle} – за {boat_time} ч. За сколько часов '
            f'проплывет {vehicle} путь от B до A?')
    return {
        "condition": task,
        "answer": boat_time2
    }


def task_3900():
    """Генерация аналогичных задач № 3900 с портала https://kuzovkin.info/one_exercise_1/3900
    Катер по течению реки прошел 87,5 км за 5 ч, а против течения это же расстояние он прошел за 7 ч.
    Какова скорость течения реки?"""
    # на 10000 проходов функции среднее количество циклов менее 3
    def _init_values():
        boat_vel = random.randint(7, 20)
        water_vel = random.randint(1, 5)
        return boat_vel, water_vel
    vehicle = random.sample(generate_context('context.json', 'vehicle'), 1)[0]
    boat_vel, water_vel = _init_values()
    while True:
        rnd = random.randint(1, 5) * 0.5
        space = np.lcm((boat_vel + water_vel), (boat_vel - water_vel)) * rnd
        if space < 100:
            break
        elif rnd == 0.5:
            boat_vel, water_vel = _init_values()
        else:
            rnd -= 0.5
    t1 = space / (boat_vel + water_vel)
    t2 = space / (boat_vel - water_vel)
    if t1.is_integer(): t1 = int(t1)
    if t2.is_integer(): t2 = int(t2)
    if space.is_integer(): space = int(space)
    task = (f'{capitalize_word(vehicle)} по течению реки {"прошёл" if find_genus_object(vehicle) == 1 else "прошла"} {space} км за {t1} ч, а против течения это '
            f'же расстояние {"он" if find_genus_object(vehicle) == 1 else "она"} {"прошёл" if find_genus_object(vehicle) == 1 else "прошла"} за {t2} ч. Какова скорость течения реки?')
    return {
        "condition": task,
        "answer": water_vel
    }


def task_7768():
    """Генерация аналогичных задач № 7768 с портала https://kuzovkin.info/one_exercise_1/7768
    Катер по течению реки прошёл 87,5 км за 5 ч, а против течения это же расстояние он прошёл за 7 ч.
    Какова собственная скорость катера?"""
    # на 10000 проходов функции среднее количество циклов менее 3
    def _init_values():
        boat_vel = random.randint(7, 20)
        water_vel = random.randint(1, 5)
        return boat_vel, water_vel
    vehicle = random.sample(generate_context('context.json', 'vehicle'), 1)[0]
    boat_vel, water_vel = _init_values()
    while True:
        rnd = random.randint(1, 5) * 0.5
        space = np.lcm((boat_vel + water_vel), (boat_vel - water_vel)) * rnd
        if space < 100:
            break
        elif rnd == 0.5:
            boat_vel, water_vel = _init_values()
        else:
            rnd -= 0.5
    t1 = space / (boat_vel + water_vel)
    t2 = space / (boat_vel - water_vel)
    if t1.is_integer(): t1 = int(t1)
    if t2.is_integer(): t2 = int(t2)
    if space.is_integer(): space = int(space)
    task = (f'{capitalize_word(vehicle)} по течению реки {"прошёл" if find_genus_object(vehicle) == 1 else "прошла"} {space} км за {t1} ч, а против течения это '
            f'же расстояние {"он" if find_genus_object(vehicle) == 1 else "она"} {"прошёл" if find_genus_object(vehicle) == 1 else "прошла"} за {t2} ч. Какова собственная '
            f'скорость {choosing_declension_form(vehicle)}?')
    return {
        "condition": task,
        "answer": boat_vel
    }


if __name__ == '__main__':
    for i in range(10):
        print(task_7768()["condition"])
    # print(task_2604())
    # print(task_3888())
    # print(task_3900())
    # print(task_7768())

    # k = 0
    # maxi = 0
    # for i in range(10000):
    #     res, j = task_3900()
    #     k += j
    #     if j > maxi:
    #         maxi = j
    # print(k / 10000, maxi)