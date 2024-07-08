import random
import numpy as np
from fractions import Fraction
from text_tasks.utils import generate_context, find_genus_object, capitalize_word, choosing_declension_form


def xround(num):
    """Устраняет ошибку точности float для чисел с не более 2мя разрядами после запятой
    возвращает int, если оно является целым числом."""
    if abs(round(num) - num) < 0.0001:
        return int(round(num))
    if abs(round(num, 1) - num) < 0.0001:
        return round(num, 1)
    if abs(round(num, 2) - num) < 0.0001:
        return round(num, 2)
    return num


def float_to_int(*args):
    """Преобразует аргументы типа float в целые числа, если они являются целыми числами, и оставляет их как float
    в противном случае."""
    return [xround(arg) for arg in args]


def _init_time():
    while True:
        _time1 = random.randint(1, 14) * 0.5
        _time2 = random.randint(1, 14) * 0.5
        if _time1 != _time2:
            return _time1, _time2


def _init_values():
    _water_vel = random.randint(1, 5)
    _boat_vel = random.randint(_water_vel + 1, 20)
    return _boat_vel, _water_vel


def task_14():
    """Генерация аналогичных задач № 14 с портала https://kuzovkin.info/one_exercise_1/14
    Расстояние между двумя пристанями равно 12,3 км. За сколько времени моторная лодка проплывет путь от одной пристани
    до другой и обратно, если собственная скорость лодки 7,2 км/ч, а скорость течения реки составляет 1/6
    скорости лодки?"""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    while True:
        water_vel_divider = random.randint(2, 6)
        water_vel = random.randint(10, 50)
        boat_vel = water_vel * water_vel_divider
        space = xround(np.lcm((water_vel + boat_vel), (water_vel - boat_vel)) * 0.1)
        if space % 1 == 0:
            water_vel, boat_vel, space = float_to_int(water_vel * 0.1, boat_vel * 0.1, space * 0.1)
            break
    time = xround((space / (water_vel + boat_vel)) + (space / (boat_vel - water_vel)))
    task = (f'Расстояние между двумя пристанями равно {space} км. За сколько времени {vehicle} проплывет путь от '
            f'одной пристани до другой и обратно, если собственная скорость {choosing_declension_form(vehicle)} '
            f'{boat_vel} км/ч, а скорость течения реки составляет 1/{water_vel_divider} '
            f'скорости {choosing_declension_form(vehicle)}?')
    return {
        "condition": task,
        "answer": time
    }


def task_38():
    """Генерация аналогичных задач № 38 с портала https://kuzovkin.info/one_exercise_1/38
    Лодка проплыла некоторое расстояние по озеру за 5 ч. Такое же расстояние плот проплывает по реке за 20 ч.
    Сколько времени затратит лодка на тот же путь по течению реки?"""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    raft = random.sample(generate_context('./text_tasks/context.json', 'raft'), 1)[0]
    water = random.sample(generate_context('./text_tasks/context.json', 'water'), 1)[0]
    while True:
        raft_time = random.randint(20, 80)
        boat_time = random.randint(1, 8)
        result_fraction = Fraction(1, boat_time) + Fraction(1, raft_time)
        if result_fraction.numerator == 1:
            boat_time2 = result_fraction.denominator
            break
    task = (f'{capitalize_word(vehicle)} {"проплыл" if find_genus_object(raft) == 1 else "проплыла"} путь по '
            f'{choosing_declension_form(water, "datv")} '
            f'за {boat_time} ч. Такое же расстояние {raft} проплывает по реке за {raft_time} ч. '
            f'Сколько времени затратит {vehicle} на тот же путь по течению реки?')
    return {
        "condition": task,
        "answer": boat_time2
    }


def task_45():
    """Генерация аналогичных задач № 45 с портала https://kuzovkin.info/one_exercise_1/45
    Собственная скорость катера равна 14,7 км, а его скорость против течения реки 10,2 км/ч.
    Какое расстояние проплывет катер, если будет двигаться 2 ч по течению реки и 4,5 ч против течения?"""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    while True:
        water_vel = xround(random.randint(10, 50) * 0.1)
        boat_vel = xround(random.randint(100, 200) * 0.1)
        time1 = xround(random.randint(10, 50) * 0.1)
        time2 = xround(random.randint(10, 50) * 0.1)
        result = xround((boat_vel + water_vel) * time1 + (boat_vel - water_vel) * time2)
        if len(str(xround(result - round(result)))) <= 3:
            break
    task = (f'Собственная скорость {choosing_declension_form(vehicle)} равна {boat_vel} км/ч, а его скорость против '
            f'течения реки {xround(boat_vel - water_vel)} км/ч. Какое расстояние проплывет {vehicle}, если будет '
            f'двигаться {time1} ч по течению реки и {time2} ч против течения?')
    return {
        "condition": task,
        "answer": result
    }


def task_2598():
    """Генерация аналогичных задач № 2598 с портала https://kuzovkin.info/one_exercise_1/2598
    Моторная лодка прошла 54 км по течению реки и 42 км против течения за то же время, что
    она проходит 96 км в стоячей воде. Найдите скорость лодки в стоячей воде, если
    скорость течения реки равна 3 км/ч."""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
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


def task_2602():
    """Генерация аналогичных задач № 2602 с портала https://kuzovkin.info/one_exercise_1/2602
    Моторная лодка прошла по течению реки расстояние 6 км, затем по озеру 10 км, затратив на весь путь 1 ч.
    С какой скоростью она шла по озеру, если скорость течения реки равна 3 км/ч?"""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    water = random.sample(generate_context('./text_tasks/context.json', 'water'), 1)[0]
    while True:
        water_vel = random.randint(2, 8)
        boat_vel = random.randint(water_vel + 2, 30)
        time1_boat_minute = random.randint(2, 5) * 10
        time2_boat_minute = 60 - time1_boat_minute
        s1 = xround((boat_vel + water_vel) * time1_boat_minute / 60)
        s2 = xround(boat_vel * time2_boat_minute / 60)
        if len(str(s1)) < 3 and len(str(s2)) < 3:
            break
    task = (f'{capitalize_word(vehicle)} {"прошел" if find_genus_object(vehicle) == 1 else "прошла"} по течению реки '
            f'расстояние {s1} км, затем по {choosing_declension_form(water, "datv")} {s2} км, затратив на весь '
            f'путь 1 ч. С какой скоростью {"он" if find_genus_object(vehicle) == 1 else "она"} '
            f'{"шел" if find_genus_object(vehicle) == 1 else "шла"}, если скорость течения реки '
            f'равна {water_vel} км/ч?')
    return {
        "condition": task,
        "answer": boat_vel
    }


def task_2604():
    """Генерация аналогичных задач № 2604 с портала https://kuzovkin.info/one_exercise_1/2604
    Турист проплыл на байдарке 15 км против течения реки и 14 км по течению, затратив на все путешествие столько же
    времени, сколько ему понадобилось бы, чтобы проплыть по озеру 30 км. Зная, что скорость течения реки равна 1 км/ч,
    найдите скорость движения туриста по озеру."""
    actor = random.sample(generate_context('./text_tasks/context.json', 'actor'), 1)[0]
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    water =  random.sample(generate_context('./text_tasks/context.json', 'water'), 1)[0]
    water_vel = random.randint(1, 6)
    boat_vel = random.randint(water_vel+1, 15)
    time1 = random.randint(1, 3)
    time2 = random.randint(1, 3)
    s1 = (boat_vel + water_vel) * time1
    s2 = (boat_vel - water_vel) * time2
    s3 = boat_vel * (time1 + time2)
    task = (f'{capitalize_word(actor)} проплыл на {choosing_declension_form(vehicle, "loct")} {s2} км против '
            f'течения реки и {s1} км по течению, затратив на все путешествие '
            f'столько же времени, сколько ему понадобилось бы, чтобы проплыть по '
            f'{choosing_declension_form(water, "datv")} {s3} км. Зная, что скорость '
            f'течения реки равна {water_vel} км/ч, найдите скорость движения '
            f'{choosing_declension_form(actor)} по {choosing_declension_form(water, "datv")}.')
    return {
        "condition": task,
        "answer": boat_vel
    }


def task_2606():
    """Генерация аналогичных задач № 2606 с портала https://kuzovkin.info/one_exercise_1/2606
    Моторная лодка прошла 7 км по течению реки и 10 км против течения, затратив на путь по течению на 0,5 ч меньше,
    чем на путь против течения. Собственная скорость лодки равна 12 км/ч. Найдите скорость хода лодки против течения."""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    water_vel = random.randint(1, 6)
    boat_vel = random.randint(water_vel+1, 15)
    while True:
        time1, time2 = _init_time()
        s1 = xround((boat_vel + water_vel) * time1)
        s2 = xround((boat_vel - water_vel) * time2)
        if isinstance(s1, int) and isinstance(s2, int):
            break
    if time1 > time2:
        flag_time = 1
    else:
        flag_time = 0
    task = (f'{capitalize_word(vehicle)} {"прошёл" if find_genus_object(vehicle) == 1 else "прошла"} {s1} '
            f'км по течению реки и {s2} км против течения, затратив на путь по течению на '
            f'{xround(time1 - time2) if flag_time else xround(time2 - time1)} ч {"больше" if flag_time else "меньше"}, '
            f'чем на путь против течения. Собственная скорость {choosing_declension_form(vehicle)} равна {boat_vel} '
            f'км/ч. Найдите скорость хода {choosing_declension_form(vehicle)} против течения.')
    return {
        "condition": task,
        "answer": boat_vel - water_vel
    }


def task_3881():
    """Генерация аналогичных задач № 3881 с портала https://kuzovkin.info/one_exercise_1/3881
    Из пункта A в пункт B по реке отплыл плот. Одновременно с ним из пункта B в пункт A вышел катер.
    Через сколько часов после выхода катер встретил плот, если катер прошел все расстояние между A и B за 15 ч,
    а плот – за 60 ч?"""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    raft = random.sample(generate_context('./text_tasks/context.json', 'raft'), 1)[0]
    dest_a, dest_b = random.sample(generate_context('./text_tasks/context.json', 'destination'), 1)[0]
    while True:
        time_raft = random.randint(15, 60)
        time_boat = random.randint(1, 14)
        time_meet = Fraction(1, Fraction(1, time_boat) + Fraction(1, time_raft))
        if time_meet.denominator == 1:
            break
    task = (f'Из {choosing_declension_form(dest_a)} в {dest_b} по реке отплыл {raft}. Одновременно с ним из '
            f'{choosing_declension_form(dest_b)} в {dest_a} вышел {vehicle}. '
            f'Через сколько часов после выхода {vehicle} встретил {raft}, если {vehicle} прошел все расстояние между '
            f'A и B за {time_boat} ч, а {raft} – за {time_raft} ч?')
    return {
        "condition": task,
        "answer": xround(time_meet)
    }


def task_3882():
    """Генерация аналогичных задач № 3882 с портала https://kuzovkin.info/one_exercise_1/3882
    Два человека отправляются из одного и того же места на прогулку до опушки леса, находящейся в 6 км от места
    отправления. Первый идёт со скоростью 4,5 км/ч, а второй − со скоростью 5,5 км/ч. Дойдя до опушки,
    второй с той же скоростью возвращается обратно. Сколько метров от опушки до места их встречи?"""
    while True:
        s_forest = random.randint(30, 70)
        s_meet = random.randint(10, s_forest - 5)
        divider = np.gcd(s_forest + s_meet, s_meet)
        if divider > 1:
            break
    s_forest /= 10
    s_meet /= 10
    v1 = s_meet / divider
    v2 = (s_forest + s_meet) / divider
    s_forest, s_meet, v1, v2 = float_to_int(s_forest, s_meet, v1, v2)
    task = (f'Два человека отправляются из одного и того же места на прогулку до опушки леса, находящейся в {s_forest} '
            f'км от места отправления. Первый идёт со скоростью {v1} км/ч, а второй - со скоростью {v2} км/ч. '
            f'Дойдя до опушки, второй с той же скоростью возвращается обратно. Сколько метров от опушки до места '
            f'их встречи?')
    return {
        "condition": task,
        "answer": xround((s_forest - s_meet) * 1000)
    }


def task_3886():
    """Генерация аналогичных задач № 3886 с портала https://kuzovkin.info/one_exercise_1/3886
    Плот и лодка движутся навстречу друг другу по реке. Они находятся на расстоянии 20 км друг другу по реке.
    Они находятся на расстоянии 20 км друг от друга. Через какое время они встретятся, если собственная скорость
    лодки 8 км/ч, а скорость течения реки 2 км/ч?"""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    raft = random.sample(generate_context('./text_tasks/context.json', 'raft'), 1)[0]
    raft_vel = random.randint(2, 10)
    boat_vel = random.randint(raft_vel + 3, 30)
    time_meet = xround(random.randint(11, 30) * 0.1)
    s_all = xround(boat_vel * time_meet)
    task = (f'{capitalize_word(raft)} и {vehicle} движутся навстречу друг другу по реке. Они находятся на расстоянии '
            f'{s_all} км друг друга. Через какое время они встретятся, если собственная скорость '
            f'{vehicle} равна {boat_vel} км/ч, а скорость {choosing_declension_form(raft)} равна {raft_vel} км/ч?')
    return {
        "condition": task,
        "answer": time_meet
    }


def task_3888():
    """Генерация аналогичных задач № 3888 с портала https://kuzovkin.info/one_exercise_1/3888
    Плот проплывает путь от A до B за 40 ч, а катер – за 4 ч. За сколько часов проплывет катер путь от B до A ?
    Аналогична задаче № 3897 с портала https://kuzovkin.info/one_exercise_1/3897
    Плот проплывает путь от A до B за 30 ч, а катер – за 5 ч. За сколько часов проплывет катер путь от B до A ?"""
    # на 10000 проходов функции среднее количество циклов менее 25
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    raft = random.sample(generate_context('./text_tasks/context.json', 'raft'), 1)[0]
    dest_a, dest_b = random.sample(generate_context('./text_tasks/context.json', 'destination'), 1)[0]
    while True:
        raft_time = random.randint(20, 80)
        boat_time = random.randint(1, 8)
        result_fraction = Fraction(1, boat_time) - Fraction(2, raft_time)
        if result_fraction.numerator == 1:
            boat_time2 = result_fraction.denominator
            break
    task = (f'{capitalize_word(raft)} проплывает путь от {choosing_declension_form(dest_a)} до '
            f'{choosing_declension_form(dest_b)} за {raft_time} ч, а {vehicle} – за {boat_time} ч. '
            f'За сколько часов проплывет {vehicle} путь от {choosing_declension_form(dest_b)} до '
            f'{choosing_declension_form(dest_a)}?')
    return {
        "condition": task,
        "answer": boat_time2
    }


def task_3889():
    """Генерация аналогичных задач № 3889 с портала https://kuzovkin.info/one_exercise_1/3889
    Катер проплывает одинаковое расстояние по озеру за 7 ч, а по течению реки – за 6 ч. Сколько времени потребуется
    плоту, чтобы проплыть такое же расстояние по этой реке?"""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    raft = random.sample(generate_context('./text_tasks/context.json', 'raft'), 1)[0]
    water = random.sample(generate_context('./text_tasks/context.json', 'water'), 1)[0]
    while True:
        time1 = random.randint(2, 8)
        time2 = random.randint(time1, 15)
        result = Fraction(1, time1) - Fraction(1, time2)
        if result.numerator == 1:
            break
    task = (f'{capitalize_word(vehicle)} проплывает одинаковое расстояние по {choosing_declension_form(water)} за '
            f'{time2} ч, а по течению реки – за {time1} ч. Сколько времени потребуется '
            f'{choosing_declension_form(raft, "datv")}, '
            f'чтобы проплыть такое же расстояние по этой реке?')
    return {
        "condition": task,
        "answer": result.denominator
    }


def task_3900():
    """Генерация аналогичных задач № 3900 с портала https://kuzovkin.info/one_exercise_1/3900
    Катер по течению реки прошел 87,5 км за 5 ч, а против течения это же расстояние он прошел за 7 ч.
    Какова скорость течения реки?
    Аналогична задаче № 8603 с портала https://kuzovkin.info/one_exercise_1/8603
    Теплоход по течению реки прошел 330 км за 12 ч, а против течения 240,5 км он прошел за 13 ч.
    Какова скорость течения реки?
    Аналогична задаче № 10182 с портала https://kuzovkin.info/one_exercise_1/10182
    Катер по течению реки прошёл 87,5 км за 5 ч, а против течения это же расстояние он прошёл за 7 ч. Какова скорость
    течения реки?
    Аналогична задаче № 10187 с портала https://kuzovkin.info/one_exercise_1/10187
    Катер по течению реки прошел 87,5 км за 5 ч, а против течения это же расстояние он прошел за 7 ч. Какова
    собственная скорость катера?
    Аналогична задаче № 10191 с портала https://kuzovkin.info/one_exercise_1/10191
    Моторная лодка прошла 80 км по течению реки за 4 ч, а против течения реки – за 5 ч. За сколько времени проплывет
    это же расстояние плот по реке?"""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
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
    t1, t2, space = float_to_int(t1, t2, space)
    task = (f'{capitalize_word(vehicle)} по течению реки {"прошёл" if find_genus_object(vehicle) == 1 else "прошла"} '
            f'{space} км за {t1} ч, а против течения это '
            f'же расстояние {"он" if find_genus_object(vehicle) == 1 else "она"} '
            f'{"прошёл" if find_genus_object(vehicle) == 1 else "прошла"} за {t2} ч. Какова скорость течения реки?')
    return {
        "condition": task,
        "answer": water_vel
    }


def task_3908():
    """Генерация аналогичных задач № 3908 с портала https://kuzovkin.info/one_exercise_1/3908
    Лодка может пройти расстояние между двумя пристанями за 1 ч 30 мин против течения реки и за 1 ч 12 мин по течению
    реки. Скорость течения реки 1,2 км/ч. Найдите расстояние между пристанями.
    Аналогична задаче № 10194 с портала https://kuzovkin.info/one_exercise_1/10194
    Лодка может пройти расстояние между двумя пристанями за 1 ч 36 мин против течения реки и за 1 ч 20 мин по
    течению реки. Скорость течения реки 1,5 км/ч. Найдите расстояние между пристанями."""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    while True:
        water_vel = random.randint(10, 50)
        boat_vel = random.randint(water_vel + 10, 200)
        space = xround(np.lcm((boat_vel + water_vel), (boat_vel - water_vel)) * random.randint(1, 5) * 0.1)
        if space < 300:
            break
    water_vel, boat_vel = xround(water_vel * 0.1), xround(boat_vel * 0.1)
    boat_vel, water_vel = float_to_int(boat_vel, water_vel)
    t1 = xround(space / (boat_vel + water_vel))
    t1_h = t1 // 60
    t1_m = t1 % 60
    t2 = xround(space / (boat_vel - water_vel))
    t2_h = t2 // 60
    t2_m = t2 % 60
    task = (f'{capitalize_word(vehicle)} может пройти расстояние между двумя пристанями за {t1_h} ч. {t1_m} мин против '
            f'течения реки и за {t2_h} ч. {t2_m} мин по течению реки. Скорость течения реки {water_vel} км/ч. '
            f'Найдите расстояние между пристанями.')
    return {
        "condition": task,
        "answer": space
    }


def task_3912():
    """Генерация аналогичных задач № 3912 с портала https://kuzovkin.info/one_exercise_1/3912
    Лодка проплыла некоторое расстояние по озеру за 5 ч. Такое же расстояние плот проплывает по реке за 20 ч.
    Сколько времени затратит лодка на тот же путь против течения реки?"""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    raft = random.sample(generate_context('./text_tasks/context.json', 'raft'), 1)[0]
    water = random.sample(generate_context('./text_tasks/context.json', 'water'), 1)[0]
    while True:
        time1 = random.randint(2, 8)
        time2 = random.randint(time1, 40)
        result = Fraction(1, time1) - Fraction(1, time2)
        if result.numerator == 1:
            break
    task = (f'{capitalize_word(vehicle)} {"проплыл" if find_genus_object(vehicle) == 1 else "проплыла"} некоторое '
            f'расстояние по {choosing_declension_form(water, "datv")} за {time1} ч. Такое же расстояние {raft} проплывает по '
            f'реке за {time2} ч. Сколько времени затратит {vehicle} на тот же путь против течения реки?')
    return {
        "condition": task,
        "answer": result.denominator
    }


def task_6472():
    """Генерация аналогичных задач № 6472 с портала https://kuzovkin.info/one_exercise_1/6472
    Турист проплыл на байдарке 24 км по озеру и 9 км против течения реки за то же время, какое понадобилось ему,
    чтобы проплыть по течению 45 км. С какой скоростью плыл турист по озеру, если скорость течения реки равна 2 км/ч?"""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    actor = random.sample(generate_context('./text_tasks/context.json', 'actor'), 1)[0]
    water = random.sample(generate_context('./text_tasks/context.json', 'water'), 1)[0]
    while True:
        boat_vel = random.randint(7, 20)
        water_vel = random.randint(1, 5)
        time1 = random.randint(2, 5)
        time2 = random.randint(2, 5)
        s = (boat_vel + water_vel) * (time1 + time2)
        if s < 100:
            break
    task = (f'{capitalize_word(actor)} проплыл на {choosing_declension_form(vehicle, "loct")} {boat_vel * time1} '
            f'км по {choosing_declension_form(water, "datv")} и {(boat_vel - water_vel) * time2} км против '
            f'течения реки за то же время, какое понадобилось чтобы проплыть по течению {s} км. '
            f'С какой скоростью плыл {actor} по {choosing_declension_form(water, "datv")}, если скорость '
            f'течения реки равна {water_vel} км/ч?')
    return {
        "condition": task,
        "answer": boat_vel
    }


def task_6473():
    """Генерация аналогичных задач № 6473 с портала https://kuzovkin.info/one_exercise_1/6473
    Лодочник проплыл 3 км по течению реки и 3 км против течения за то же время, за которое плот мог бы проплыть 4 км
    по течению. Собственная скорость лодки равна 6 км/ч. Найдите скорость течения реки."""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    actor = random.sample(generate_context('./text_tasks/context.json', 'actor'), 1)[0]
    raft = random.sample(generate_context('./text_tasks/context.json', 'raft'), 1)[0]
    boat_vel = random.randint(7, 20)
    water_vel = random.randint(1, 5)
    time1 = random.randint(2, 10)
    time2 = random.randint(2, 10)
    task = (f'{capitalize_word(actor)} проплыл {time1 * (water_vel + boat_vel)} и {time2 * (boat_vel - water_vel)} км '
            f'км против течения реки за то же время, за которое {raft} '
            f'{"мог" if find_genus_object(raft) == 1 else "могла" if find_genus_object(raft) == 2 else "могло"} бы '
            f'проплыть {water_vel * (time1 + time2)} км по течению. Собственная скорость '
            f'{choosing_declension_form(vehicle)} равна {boat_vel} км/ч. Найдите скорость течения реки.')
    return {
        "condition": task,
        "answer": water_vel
    }


def task_6476():
    """Генерация аналогичных задач № 6476 с портала https://kuzovkin.info/one_exercise_1/6476
    Моторная лодка прошла 20 км против течения реки и 14 км по озеру, затратив на путь по озеру на 1 ч меньше, чем на
    путь по реке. Скорость течения реки равна 4 км/ч. Найдите скорость хода лодки против течения."""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    water = random.sample(generate_context('./text_tasks/context.json', 'water'), 1)[0]
    water_vel = random.randint(1, 6)
    boat_vel = random.randint(water_vel + 1, 15)
    flag_time = 0
    while True:
        time1, time2 = _init_time()
        s1 = xround((boat_vel - water_vel) * time1)
        s2 = xround(boat_vel * time2)
        if isinstance(s1, int) and isinstance(s2, int):
            break
    if time1 > time2:
        flag_time = 1
    task = (f'{capitalize_word(vehicle)} {"прошёл" if find_genus_object(vehicle) == 1 else "прошла"} {s1} км '
            f'против течения реки и {s2} км по {choosing_declension_form(water, "datv")}, затратив на путь '
            f'по {choosing_declension_form(water, "datv")} на {xround(abs(time1 - time2))} ч '
            f'{"меньше" if flag_time else "больше"}, чем на путь по реке. Скорость течения реки равна {water_vel} '
            f'км/ч. Найдите скорость хода {choosing_declension_form(vehicle)} против течения.')
    return {
        "condition": task,
        "answer": boat_vel - water_vel
    }


def task_6481():
    """Генерация аналогичных задач № 6481 с портала https://kuzovkin.info/one_exercise_1/6481
    Колонне автомашин было дано задание перевезти со склада в речной порт 60 т груза. В связи с неблагоприятной погодой
    на каждую машину пришлось грузить на 0,5 т меньше, чем предполагалось, и поэтому колонну дополнили еще
    четырьмя машинами. Сколько машин было в колонне первоначально?"""
    while True:
        vehicle_num = random.randint(15, 30)
        vehicle_delta = random.randint(3, 7)
        mass = np.lcm(vehicle_num, (vehicle_num + vehicle_delta)) * random.randint(2, 4)
        if mass < 1000 and mass % 10 == 0:
            break
    mass //= 10
    delta = xround(mass / vehicle_num - mass / (vehicle_num + vehicle_delta))
    task = (f'Колонне автомашин было дано задание перевезти со склада в речной порт {mass} т груза. В связи с '
            f'неблагоприятной погодой на каждую машину пришлось грузить на {delta} т меньше, чем предполагалось, и '
            f'поэтому колонну дополнили еще {vehicle_delta} машинами. Сколько машин было в колонне первоначально?')
    return {
        "condition": task,
        "answer": vehicle_num
    }


def task_7757():
    """Генерация аналогичных задач № 7757 с портала https://kuzovkin.info/one_exercise_1/7757
    Собственная скорость катера 25,5 км/ч, скорость течения 2,5 км/ч. Какой путь пройдёт катер за полтора
    часа против течения?"""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    water_vel = random.randint(10, 100)
    boat_vel = xround(random.randint(water_vel + 50, 400) * 0.1)
    water_vel = xround(water_vel * 0.1)
    time = xround(random.randint(3, 7) * 0.5)
    task = (f'Собственная скорость {choosing_declension_form(vehicle)} равна {boat_vel} км/ч, '
            f'cкорость течения {water_vel} км/ч. Какой путь пройдёт катер за {time} против течения?')
    return {
        "condition": task,
        "answer": xround((boat_vel - water_vel) * 2)
    }


def task_7764():
    """Генерация аналогичных задач № 7764 с портала https://kuzovkin.info/one_exercise_1/7764
    Из пунктов A и B одновременно навстречу друг другу вышли плот и катер. Катер встретил плот через 4 ч после выхода,
    а еще через 20 мин прибыл в пункт B. Сколько времени плыл плот из B в A ?
    Аналогична задаче № 7767 с портала https://kuzovkin.info/one_exercise_1/7767
    Из пунктов A и B одновременно навстречу друг другу вышли плот и катер. Катер встретил плот через 4 ч после выхода,
    а еще через 20 мин прибыл в пункт B . Сколько времени плыл плот из B в A ?"""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    raft = random.sample(generate_context('./text_tasks/context.json', 'raft'), 1)[0]
    dest_a, dest_b = random.sample(generate_context('./text_tasks/context.json', 'destination'), 1)[0]
    while True:
        boat_time = random.randint(1, 7) * 60
        raft_time = random.randint(1, 5) * 10
        if boat_time % raft_time == 0:
            vel_diff = boat_time // raft_time
            raft_time1 = xround((boat_time + raft_time) * vel_diff / 60)
            if raft_time1 < 100:
                break

    task = (f'Из {choosing_declension_form(dest_a)} и {choosing_declension_form(dest_b)} одновременно навстречу друг '
            f'другу вышли {raft} и {vehicle}. {capitalize_word(vehicle)} '
            f'{"встретил" if find_genus_object(vehicle) == 1 else "встретила"} {raft} через {boat_time // 60} ч. после '
            f'выхода, а еще через {raft_time} мин. '
            f'{"прибыл" if find_genus_object(vehicle) == 1 else "прибыла"} {raft} в пункт '
            f'B. Сколько времени '
            f'{"плыл" if find_genus_object(raft) == 1 else "плыла" if find_genus_object(raft) == 2 else "плыло"} '
            f'{raft} из {choosing_declension_form(dest_b)} в {dest_a}?')
    return {
        "condition": task,
        "answer": raft_time1
    }


def task_7768():
    """Генерация аналогичных задач № 7768 с портала https://kuzovkin.info/one_exercise_1/7768
    Катер по течению реки прошёл 87,5 км за 5 ч, а против течения это же расстояние он прошёл за 7 ч.
    Какова собственная скорость катера?"""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
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
    t1, t2, space = float_to_int(t1, t2, space)
    task = (f'{capitalize_word(vehicle)} по течению реки {"прошёл" if find_genus_object(vehicle) == 1 else "прошла"} '
            f'{space} км за {t1} ч, а против течения это '
            f'же расстояние {"он" if find_genus_object(vehicle) == 1 else "она"} '
            f'{"прошёл" if find_genus_object(vehicle) == 1 else "прошла"} за {t2} ч. Какова собственная '
            f'скорость {choosing_declension_form(vehicle)}?')
    return {
        "condition": task,
        "answer": boat_vel
    }


def task_7770():
    """Генерация аналогичных задач № 7770 с портала https://kuzovkin.info/one_exercise_1/7770
    Теплоход по течению реки прошел 330 км за 12 ч, а против течения 240,5 км он прошел за 13 ч. Какова собственная
    скорость теплохода?"""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    water_vel = random.randint(1, 10)
    boat_vel = random.randint(water_vel + 5, 30)
    time1 = random.randint(1, 15)
    while True:
        time2 = random.randint(1, 15)
        if time1 != time2:
            break
    task = (f'{capitalize_word(vehicle)} по течению реки {"прошёл" if find_genus_object(vehicle) == 1 else "прошла"} '
            f'{time1 * (boat_vel + water_vel)} км за {time1} ч, а против течения {time2 * (boat_vel - water_vel)} км '
            f'{"он" if find_genus_object(vehicle) == 1 else "она"} '
            f'{"прошёл" if find_genus_object(vehicle) == 1 else "прошла"} за {time2} ч. Какова собственная '
            f'скорость {choosing_declension_form(vehicle)}?')
    return {
        "condition": task,
        "answer": boat_vel
    }


def task_7776():
    """Генерация аналогичных задач № 7776 с портала https://kuzovkin.info/one_exercise_1/7776
    Моторная лодка прошла 90 км по течению реки за 6 ч, а против течения реки – за 10 ч.
    За сколько времени проплывет это же расстояние плот по реке?"""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    raft = random.sample(generate_context('./text_tasks/context.json', 'raft'), 1)[0]
    boat_vel, water_vel = _init_values()
    while True:
        space = np.lcm.reduce([(boat_vel + water_vel), (boat_vel - water_vel), water_vel]) * random.randint(1, 3)
        if space < 150 and xround(space / water_vel) < 100:
            break
        boat_vel, water_vel = _init_values()
    t1 = xround(space / (boat_vel + water_vel))
    t2 = xround(space / (boat_vel - water_vel))
    task = (f'{capitalize_word(vehicle)} {"прошёл" if find_genus_object(vehicle) == 1 else "прошла"} {space} км '
            f'по течению реки за {t1} ч, а против течения реки - за {t2} ч. За сколько времени проплывет это же '
            f'расстояние {raft} по реке?')
    return {
        "condition": task,
        "answer": xround(space / water_vel)
    }


def task_7784():
    """Генерация аналогичных задач № 7784 с портала https://kuzovkin.info/one_exercise_1/7784
    Лодка проплыла некоторое расстояние по озеру за 4 ч. Такое же расстояние плот проплывает по реке за 12 ч.
    Сколько времени затратит лодка на тот же путь по течению реки?"""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    raft = random.sample(generate_context('./text_tasks/context.json', 'raft'), 1)[0]
    water = random.sample(generate_context('./text_tasks/context.json', 'water'), 1)[0]
    while True:
        boat_vel, water_vel = _init_values()
        space = np.lcm.reduce([(boat_vel + water_vel), boat_vel, water_vel]) * random.randint(1, 3)
        if space < 150 and xround(space / water_vel) < 100:
            break
    t1 = xround(space / boat_vel)
    t2 = xround(space / water_vel)
    task = (f'{capitalize_word(vehicle)} {"проплыл" if find_genus_object(vehicle) == 1 else "проплыла"} некоторое '
            f'расстояние по {choosing_declension_form(water, "datv")} за {t1} ч. Такое же расстояние плот '
            f'проплывает по реке за {t2} ч. Сколько времени '
            f'затратит {vehicle} на тот же путь по течению реки?')
    return {
        "condition": task,
        "answer": xround(space / (boat_vel + water_vel))
    }


def task_7790():
    """Генерация аналогичных задач № 7790 с портала https://kuzovkin.info/one_exercise_1/7790
    Собственная скорость теплохода равна 32,5 км, а его скорость по течению реки 35 км/ч.
    Какое расстояние проплывет теплоход, если будет двигаться 2,6 ч по течению реки и 0,8 ч против течения?"""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    water_vel = random.randint(2, 8)
    boat_vel = random.randint(water_vel + 5, 45)
    t1 = xround(random.randint(1, 50) * 0.1)
    while True:
        t2 = xround(random.randint(1, 50) * 0.1)
        if xround(t2) != xround(t1):
            break
    task = (f'Собственная скорость {vehicle} равна {boat_vel} км/ч, а его скорость по течению реки '
            f'{boat_vel + water_vel} км/ч. Какое расстояние проплывет {vehicle}, если будет двигаться {t1} ч по '
            f'течению реки и {t2} ч против течения?')
    return {
        "condition": task,
        "answer": xround(t1 * (boat_vel + water_vel) + t2 * (boat_vel - water_vel))
    }


def task_7796():
    """Генерация аналогичных задач № 7796 с портала https://kuzovkin.info/one_exercise_1/7796
    От лесоповала вниз по течению реки движется со скоростью 3 км/ч плот.
    Плотовщик доплывает на моторке из конца плота к его началу и обратно за 16 минут 40 секунд. Найдите длину плота,
    если собственная скорость моторки равна 15 км/ч. Ответ дайте в километрах."""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    raft = random.sample(generate_context('./text_tasks/context.json', 'raft'), 1)[0]
    while True:
        water_vel = random.randint(1, 5)
        boat_vel = random.randint(water_vel + 2, 20)
        raft_l = random.randint(1, 5)
        time = xround(((raft_l / (boat_vel + water_vel)) + (raft_l / (boat_vel - water_vel))) * 3600)
        if isinstance(time, int):
            break
    time_m = time // 60
    timre_s = time % 60
    task = (f'От лесоповала вниз по течению реки движется со скоростью {water_vel} км/ч {raft}. Плотовщик доплывает на '
            f'{choosing_declension_form(vehicle, "loct")} из конца {choosing_declension_form(raft)} к его началу '
            f'и обратно за {time_m} минут {timre_s} секунд. Найдите длину {choosing_declension_form(raft)}, если '
            f'собственная скорость {choosing_declension_form(vehicle)} равна {boat_vel} км/ч. Ответ дайте в километрах.')
    return {
        "condition": task,
        "answer": raft_l
    }


def task_8611():
    """Генерация аналогичных задач № 8611 с портала https://kuzovkin.info/one_exercise_1/8611
    Моторная лодка прошла 80 км по течению реки за 4 ч, а против течения реки – за 5 ч. За сколько времени проплывет
    это же расстояние моторная лодка по озеру?
    Аналогична задаче № 7777 с портала https://kuzovkin.info/one_exercise_1/7777
    Моторная лодка прошла 90 км по течению реки за 6 ч, а против течения реки – за 10 ч. За сколько времени проплывет
    это же расстояние моторная лодка по озеру?"""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    water = random.sample(generate_context('./text_tasks/context.json', 'water'), 1)[0]
    boat_vel, water_vel = _init_values()
    while True:
        space = np.lcm.reduce([(boat_vel + water_vel), (boat_vel - water_vel), boat_vel])
        if space < 150:
            break
        else:
            boat_vel, water_vel = _init_values()
    time1 = space // (boat_vel + water_vel)
    time2 = space // (boat_vel - water_vel)
    task = (f'{capitalize_word(vehicle)} {"прошёл" if find_genus_object(vehicle) == 1 else "прошла"} {space} км '
            f'за {time1} ч по течению реки, а против течения реки - за {time2} ч, За сколько времени проплывет '
            f'это же расстояние {vehicle} по {choosing_declension_form(water, "datv")}?')
    return {
        "condition": task,
        "answer": f'{space // boat_vel}'
    }


def task_8620():
    """Генерация аналогичных задач № 8620 с портала https://kuzovkin.info/one_exercise_1/8620
    Собственная скорость теплохода равна 32,5 км, а его скорость по течению реки 35 км/ч.
    С какой скоростью течет река?"""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    water_vel = random.randint(2, 8)
    boat_vel = random.randint(15, 45)
    task = (f'Собственная скорость {choosing_declension_form(vehicle)} равна {boat_vel} км/ч, '
            f'а {"его" if find_genus_object(vehicle) == 1 else "её"} скорость по течению реки {boat_vel + water_vel} '
            f'км/ч. С какой скоростью течет река?')
    return {
        "condition": task,
        "answer": water_vel
    }


def task_8621():
    """Генерация аналогичных задач № 8621 с портала https://kuzovkin.info/one_exercise_1/8621
    Собственная скорость теплохода равна 32,5 км, а его скорость по течению реки 35 км/ч. Какова скорость теплохода
    против течения реки?"""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    water_vel = random.randint(2, 8)
    boat_vel = random.randint(15, 45)
    task = (f'Собственная скорость {choosing_declension_form(vehicle)} равна {boat_vel} км/ч, '
            f'а {"его" if find_genus_object(vehicle) == 1 else "её"} скорость по течению реки {boat_vel + water_vel} '
            f'км/ч. Какова скорость {choosing_declension_form(vehicle)} против течения реки?')
    return {
        "condition": task,
        "answer": (boat_vel - water_vel)
    }


def task_8623():
    """Генерация аналогичных задач № 8623 с портала https://kuzovkin.info/one_exercise_1/8623
    Собственная скорость катера равна 14,7 км, а его скорость против течения реки 10,2 км/ч.
    С какой скоростью течет река?"""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    water_vel = xround(random.randint(10, 100) * 0.1)
    boat_vel = xround(random.randint(80, 400) * 0.1)
    task = (f'Собственная скорость {choosing_declension_form(vehicle)} равна {boat_vel} км/ч, '
            f'а {"его" if find_genus_object(vehicle) == 1 else "её"} скорость против течения реки '
            f'{xround(boat_vel - water_vel)} км/ч. С какой скоростью течет река?')
    return {
        "condition": task,
        "answer": water_vel
    }


def task_10171():
    """Генерация аналогичных задач № 10171 с портала https://kuzovkin.info/one_exercise_1/10171
    Собственная скорость лодки 8,5 км/ч, а скорость течения 3,5 км/ч. Расстояние между пристанями 15 км.
    Сколько времени затратит лодка на путь между пристанями туда и обратно?"""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    while True:
        water_vel = random.randint(10, 100)
        boat_vel = random.randint(water_vel + 10, 400)
        space = np.lcm((boat_vel + water_vel), (boat_vel - water_vel))
        if space < 1000:
            break
    water_vel = xround(water_vel / 10)
    boat_vel = xround(boat_vel / 10)
    space = xround(space / 10)
    time = xround(space / (boat_vel + water_vel) + space / (boat_vel - water_vel))
    task = (f'Собственная скорость {choosing_declension_form(vehicle)} равна {boat_vel} км/ч, '
            f'а скорость течения {water_vel} км/ч. Расстояние между пристанями {space} км. '
            f'Сколько времени затратит {vehicle} на путь между пристанями туда и обратно?')
    return {
        "condition": task,
        "answer": time
    }


def task_10195():
    """Генерация аналогичных задач № 10195 с портала https://kuzovkin.info/one_exercise_1/10195
    Лодка может пройти расстояние между двумя пристанями за 1 ч 30 мин против течения реки и за 1 ч 12 мин по течению
    реки. Скорость течения реки 1,2 км/ч. Найдите собственную скорость лодки."""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    while True:
        water_vel = random.randint(10, 50)
        boat_vel = random.randint(water_vel + 10, 200)
        space = xround(np.lcm((boat_vel + water_vel), (boat_vel - water_vel)) * random.randint(1, 5) * 0.1)
        if space < 300:
            break
    water_vel, boat_vel = xround(water_vel * 0.1), xround(boat_vel * 0.1)
    t1 = xround(space / (boat_vel + water_vel))
    t1_h = t1 // 60
    t1_m = t1 % 60
    t2 = xround(space / (boat_vel - water_vel))
    t2_h = t2 // 60
    t2_m = t2 % 60
    task = (f'Лодка может пройти расстояние между двумя пристанями за {t1_h} ч {t1_m} мин против течения реки '
            f'и за {t2_h} ч {t2_m} мин по течению реки. Скорость течения реки {water_vel} км/ч. '
            f'Найдите собственную скорость {vehicle}?')
    return {
        "condition": task,
        "answer": boat_vel
    }


def task_10210():
    """Генерация аналогичных задач № 10210 с портала https://kuzovkin.info/one_exercise_1/10210
    От лесоповала вниз по течению реки движется плот длиной 1 км. Плотовщик доплывает на моторке из конца плота к его
    началу и обратно за 8 минут 20 секунд. Найдите скорость плота, если собственная скорость моторки равна 15 км/ч.
    Ответ дайте в км/ч."""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    raft = random.sample(generate_context('./text_tasks/context.json', 'raft'), 1)[0]
    while True:
        water_vel = random.randint(1, 5)
        boat_vel = random.randint(water_vel + 2, 20)
        raft_l = random.randint(1, 5)
        time = xround(((raft_l / (boat_vel + water_vel)) + (raft_l / (boat_vel - water_vel))) * 3600)
        if isinstance(time, int):
            break
    time_m = time // 60
    timre_s = time % 60
    task = (f'От лесоповала {raft} вниз по течению реки движется плот длиной {raft_l} км. '
            f'Плотовщик доплывает на {choosing_declension_form(vehicle, "loct")} из конца {raft} к его началу '
            f'и обратно за {time_m} мин {timre_s} сек. Найдите скорость {choosing_declension_form(raft)}, если'
            f'собственная скорость {choosing_declension_form(vehicle)} равна {boat_vel} км/ч? Ответ дайте в км/ч.')
    return {
        "condition": task,
        "answer": water_vel
    }


def task_12774():
    """Генерация аналогичных задач № 12774 с портала https://kuzovkin.info/one_exercise_1/12774
    Прогулочный теплоход отправился от пристани А к пристани В вниз по течению реки. После получасовой стоянки в B он
    отправился обратно и через 8 ч после отплытия из А вернулся к той же пристани. Какова собственная скорость
    теплохода, если расстояние между пристанями А и B равно 36 км, а скорость течения реки равна 2 км/ч"""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    dest_a, dest_b = random.sample(generate_context('./text_tasks/context.json', 'destination'), 1)[0]
    while True:
        water_vel = random.randint(1, 5)
        boat_vel = random.randint(water_vel + 2, 20)
        time_stop = random.randint(0, 1)
        space = xround(np.lcm.reduce([(boat_vel + water_vel), (boat_vel - water_vel), boat_vel]) * 0.5)
        time = xround(((space / (boat_vel + water_vel)) + (space / (boat_vel - water_vel))) +
                      (0.5 if time_stop else 1))
        if isinstance(time, int) and time < 30:
            break
    task = (f'{capitalize_word(vehicle)} отправился от {choosing_declension_form(dest_a)} к '
            f'{choosing_declension_form(dest_b, "datv")} вниз по течению реки. После '
            f'{"получасовой" if time_stop else "часовой"} стоянки в B он отправился обратно и через {time} ч '
            f'после отплытия из А вернулся к той же пристани. Какова собственная скорость '
            f'{choosing_declension_form(vehicle)}, если расстояние между '
            f'{choosing_declension_form(dest_a, "ablt")} и '
            f'{choosing_declension_form(dest_b, "ablt")} равно {space} км, '
            f'а скорость течения реки равна {water_vel} км/ч?')
    return {
        "condition": task,
        "answer": boat_vel
    }


def task_12778():
    """Генерация аналогичных задач № 12778 с портала https://kuzovkin.info/one_exercise_1/12778
    Катер прошел по течению реки 8 км и 16 км против течения реки, затратив на весь путь 4/3 часа. Какова скорость
    катера по течению, если собственная скорость катера равна 20 км/ч?"""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    while True:
        water_vel = random.randint(1, 5)
        boat_vel = random.randint(water_vel + 2, 20)
        while True:
            time_denom = random.randint(2, 5)
            t1_nom = random.randint(1, time_denom - 1)
            t2_nom = random.randint(1, time_denom - 1)
            if Fraction((t1_nom + t2_nom), time_denom).denominator != 1:
                break
        space1 = xround((boat_vel + water_vel) * Fraction(t1_nom, time_denom))
        space2 = xround((boat_vel - water_vel) * Fraction(t2_nom, time_denom))
        if isinstance(space1, int) and isinstance(space2, int):
            break
    task = (f'{capitalize_word(vehicle)} {"прошёл" if find_genus_object(vehicle) == 1 else "прошла"} по течению '
            f'реки {space1} км и {space2} км против течения реки, затратив на весь путь '
            f'{Fraction(t1_nom + t2_nom, time_denom)} часа. Какова скорость {choosing_declension_form(vehicle)} по '
            f'течению, если собственная скорость {choosing_declension_form(vehicle)} равна {boat_vel} км/ч?')
    return {
        "condition": task,
        "answer": boat_vel + water_vel
    }


def task_12780():
    """Генерация аналогичных задач № 12780 с портала https://kuzovkin.info/one_exercise_1/12780
    Пункты А,Б,С расположены на реке в указанном порядке вниз по течению. Расстояние между А и Б равно 4 км, а между Б
    и С - 14 км. В 12 часов из пункта Б отплыла лодка и направилась в пункт А. Достигнув пункта А, она сразу же
    повернула назад и в 14 часов прибыла в пункт С. Скорость течения - 5 км/ч. Найти скорость лодки в стоячей воде."""
    vehicle = random.sample(generate_context('./text_tasks/context.json', 'vehicle'), 1)[0]
    while True:
        space1 = random.randint(3, 8)
        space2 = random.randint(10, 20)
        water_vel = random.randint(2, 6)
        boat_vel = random.randint(water_vel + 2, water_vel + 7)
        time1 = xround(space1 / (boat_vel - water_vel))
        time2 = xround((space1 + space2) / (boat_vel + water_vel))
        time_total = xround(time1 + time2)
        if isinstance(time_total, int):
            break
    start_hour = random.randint(8, 14)
    end_hour = start_hour + time_total
    task = (f'Пункты А,Б,С расположены на реке в указанном порядке вниз по течению. Расстояние между А и Б равно '
            f'{space1} км, а между Б и С - {space2} км. В {start_hour} часов из пункта Б отплыла лодка и направилась в '
            f'пункт А. Достигнув пункта А, она сразу же повернула назад и в {end_hour} часов прибыла в пункт С. '
            f'Скорость течения - {water_vel} км/ч. Найти скорость {choosing_declension_form(vehicle)} в стоячей воде.')
    return {
        "condition": task,
        "answer": boat_vel
    }
