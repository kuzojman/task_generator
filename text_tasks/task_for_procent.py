import numpy as np
import random
from .utils import choosing_declension_form, capitalize_word, find_number_object, find_genus_object, generate_context, write_numeral_word, fraction_latex_format


def task_642():
    '''Генерация аналогичных задач № 642 с портала https://kuzovkin.info/one_exercise_1/642
    Мельхиор − общее название группы сплавов на основе меди, содержащих никель, железо и марганец.
    В мельхиоре содержится 33% никеля, 1% железа и 1% марганца. Сколько процентов меди содержится в сплаве?'''
    metal, metal_1, metal_2, metal_3 = random.sample(generate_context('./text_tasks/context.json', 'metals'), 4)
    while True:
        number, number1, number2 = np.random.randint(1, 95, size=3)
        result = 100 - (number + number1 + number2)
        if  45 < result < 95 and result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'Группы сплавов на основе {choosing_declension_form(metal)}, содержащих {choosing_declension_form(metal_1)}, {choosing_declension_form(metal_2)} и {choosing_declension_form(metal_3)}. В сплаве содержится {number}% {choosing_declension_form(metal_1, "gent")}, {number1}% {choosing_declension_form(metal_2, "gent")} и {number2}% {choosing_declension_form(metal_3, "gent")}. Сколько процентов {choosing_declension_form(metal, "gent")} содержится в сплаве? '
    return task, answer


def task_645():
    '''Генерация аналогичных задач № 645 с портала https://kuzovkin.info/one_exercise_1/645
    Воздух состоит из азота (78,09% по объёму), кислорода (20,95%), углекислого газа (0,03%).
    Кроме этих газов, в воздухе содержатся ещё так называемые инертные газы: аргон, неон, гелий, криптон, радон.
    Каково процентное содержание инертных газов в воздухе?'''
    gas, gas_1, gas_2, gas_3, gas_4, gas_5, gas_6, gas_7 = random.sample(generate_context('./text_tasks/context.json', 'gases'), 8)
    while True:
        number, number1, number2 = round(np.random.uniform(1, 95), 2), round(np.random.uniform(1, 95), 2), round(np.random.uniform(1, 95), 2)
        if number * 10 % 10 == 0 or number1 * 10 % 10 == 0 or number2 * 10 % 10 == 0:
          continue
        result = 100 - (number + number1 + number2)
        if  0 < result < 95 and len(str(result)) <= 5 and result * 10 % 10 != 0:
            answer = result
            break
    task = f'Смесь газов состоит из {choosing_declension_form(gas)} ({number}% по объёму), {choosing_declension_form(gas_1)} ({number1}%), {choosing_declension_form(gas_2)} ({number2}%). Кроме этих газов, содержатся ещё: {gas_3}, {gas_4}, {gas_5}, {gas_6}, {gas_7}. Каково процентное содержание этих газов?'
    return task, answer


def task_930():
    '''Генерация аналогичных задач № 930 с портала https://kuzovkin.info/one_exercise_1/930
    При анализе куска угля весом в 7 г обнаружили, что он содержит 5,2 г углерода, 0,5 г водорода, 0,42 г кислорода,
    0,28 г азота, остальное составляет зола. Определить процентное содержание указанных веществ в угле.'''
    gas, gas_1, gas_2, gas_3 = random.sample(generate_context('./text_tasks/context.json', 'gases'), 4)
    while True:
        number, number1, number2, number3, number4 = round(np.random.uniform(0, 10), 1),  round(np.random.uniform(0, 10), 1), round(np.random.uniform(0, 10), 2), round(np.random.uniform(0, 10), 2), round(np.random.uniform(0, 10), 1)
        result = number + number1 + number2 + number3 + number4

        if  1 < result < 30 and len(str(result)) <= 3:
            ans, ans1, ans2, ans3 = round(number * 100 / result, 2), round(number1 * 100 / result, 2), round(number2 * 100 / result, 2), round(number3 * 100 / result, 2)
            answer = f'{ans}:{ans1}:{ans2}:{ans3}'
            break
    task = f'При анализе вещества весом в {result} г обнаружили, что он содержит {number} г {choosing_declension_form(gas)}, {number1} г {choosing_declension_form(gas_1)}, {number2} г {choosing_declension_form(gas_2)}, {number3} г {choosing_declension_form(gas_3)}, остальное составляет зола. Определить процентное содержание указанных веществ.'
    return task, answer


def task_1039():
    '''Генерация аналогичных задач № 1039 с портала https://kuzovkin.info/one_exercise_1/1039
    В растворе массой 280 г содержится 56 г соли. Какова концентрация этого раствора?'''
    product = np.random.choice(generate_context('./text_tasks/context.json', 'products'))
    while True:
        number, number1 = np.random.randint(1, 1000, size=2)
        if number <= number1:
          continue
        result = number1 * 100 / number
        if  0 < result < 95 and result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'В растворе массой {number} г содержится {number1} г {choosing_declension_form(product)}. Какова концентрация этого раствора?'
    return task, answer


def task_1047():
    '''Генерация аналогичных задач № 1047 с портала https://kuzovkin.info/one_exercise_1/1047
    В семенах подсолнечника нового сорта содержится 49,5% масла.
    Сколько килограммов таких семян надо взять, чтобы в них содержалось 29,7 кг масла?'''
    oil = np.random.choice(generate_context('./text_tasks/context.json', 'oils'))
    while True:
        number, number1 = np.random.randint(1, 100, size=2)
        if number <= number1:
          continue
        result = number1 * 100 / number
        if  0 < result < 95 and result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'В семенах {choosing_declension_form(oil)} нового сорта содержится {number}% масла. Сколько килограммов таких семян надо взять, чтобы в них содержалось {number1} кг масла?'
    return task, answer


def task_611():
    '''Генерация аналогичных задач № 611 с портала https://kuzovkin.info/one_exercise_1/611
    Оптовая цена товара на складе 5500 р. Торговая надбавка в магазине составляет 12%.
    Сколько стоит этот товар в магазине?'''
    while True:
        number, number1 = np.random.randint(100, 100000), np.random.randint(1, 100)
        result = (number / 100 * number1) + number
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'Оптовая цена товара на складе {number} р. Торговая надбавка в магазине составляет {number1}%. Сколько стоит этот товар в магазине?'
    return task, answer


def task_621():
    '''Генерация аналогичных задач № 621 с портала https://kuzovkin.info/one_exercise_1/621
    Проезд в маршрутке от станции метро Университет до ГЗ МГУ имени М. В. Ломоносова подорожал с 20 рублей до 25 рублей.
    На сколько процентов повысилась цена проезда?'''
    transport = np.random.choice(generate_context('./text_tasks/context.json', 'transports'))
    while True:
        number, number1 = np.random.randint(10, 100, size=2)
        if number >= number1:
          continue
        result = ((number1 - number) / number) * 100
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'Проезд на {choosing_declension_form(transport, "loct")} подорожал с {number} рублей до {number1} рублей. На сколько процентов повысилась цена проезда?'
    return task, answer


def task_626():
    '''Генерация аналогичных задач № 626 с портала https://kuzovkin.info/one_exercise_1/626
    Цена на товар повысилась на 15% и составила 2944 рубля. Найдите первоначальную цену товара'''
    while True:
        number, number1 = np.random.randint(10, 100), np.random.randint(10, 10000)
        if number >= number1:
          continue
        result = (number1 * 100) / (100 + number)
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'Цена на товар повысилась на {number}% и составила {number1} рубля. Найдите первоначальную цену товара'
    return task, answer


def task_638():
    '''Генерация аналогичных задач № 638 с портала https://kuzovkin.info/one_exercise_1/638
    В голосовании приняли участие 64,3% электората. Сколько процентов электората не пришли на выборы?'''
    value = np.random.choice(['элеторат', 'жители', 'население'])
    while True:
        number = np.random.randint(1, 100)
        result = 100 - number
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'В голосовании приняли участие {number}% {choosing_declension_form(value)}. Сколько процентов {choosing_declension_form(value)} не пришли на выборы?'
    return task, answer


def task_647():
    '''Генерация аналогичных задач № 647 с портала https://kuzovkin.info/one_exercise_1/647
    Найдите число, 17% которого на 27 больше 14% его.'''
    while True:
        number, number1, number2 = np.random.randint(1, 90, size=3)
        if number <= number2:
          continue
        result = (number1 / (number - number2)) * 100
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'Найдите число, {number}% которого на {number1} больше {number2}% его.'
    return task, answer


def task_659():
    '''Генерация аналогичных задач № 659 с портала https://kuzovkin.info/one_exercise_1/659
    Найдите: 140% от 365'''
    while True:
        number, number1 = np.random.randint(1, 1000, size=2)
        result = (number1 * number) / 100
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'Найдите: {number}% от {number1}'
    return task, answer


def task_661():
    '''Генерация аналогичных задач № 661 с портала https://kuzovkin.info/one_exercise_1/661
    Найдите: 130,5% от 1500'''
    while True:
        number, number1 = round(np.random.uniform(10, 300), 2), np.random.randint(100, 5000)
        if number * 10 % 10 == 0:
          continue
        result = (number1 * number) / 100
        if len(str(result)) <= 5 and result * 10 % 10 != 0:
            answer = result
            break
    task = f'Найдите: {number}% от {number1}'
    return task, answer


def task_673():
    '''Генерация аналогичных задач № 673 с портала https://kuzovkin.info/one_exercise_1/673
    Найдите: 3,75% от 18,4'''
    while True:
        number, number1 = round(np.random.uniform(10, 300), 2), round(np.random.uniform(10, 300), 2)
        if number * 10 % 10 == 0 or number1 * 10 % 10 == 0:
          continue
        result = (number1 * number) / 100
        if len(str(result)) <= 5 and result * 10 % 10 != 0:
            answer = result
            break
    task = f'Найдите: {number}% от {number1}'
    return task, answer


def task_682():
    '''Генерация аналогичных задач № 682 с портала https://kuzovkin.info/one_exercise_1/682
    Найдите целое, если 4% равны 28'''
    while True:
        number, number1 = np.random.randint(1, 90, size=2)
        if number == number1:
          continue
        result = (number1 * 100) / number
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'Найдите целое, если {number}% равны {number1}'
    return task, answer


def task_722():
    '''Генерация аналогичных задач № 722 с портала https://kuzovkin.info/one_exercise_1/722
    Переведите проценты в десятичную дробь: 5,7%'''
    while True:
        number = round(np.random.uniform(1, 100), 2)
        if number * 10 % 10 == 0:
          continue
        result = number / 100
        if len(str(result)) <= 6 and result * 10 % 10 != 0:
            answer = result
            break
    task = f'Переведите проценты в десятичную дробь: {number}%'
    return task, answer


def task_757():
    '''Генерация аналогичных задач № 757 с портала https://kuzovkin.info/one_exercise_1/757
    Переведите дроби в проценты: 0,004'''
    while True:
        number = round(np.random.uniform(0, 1), 3)
        if number * 10 % 10 == 0:
          continue
        result = number * 100
        if 0 <= result <= 99 and len(str(result)) <= 6 and result * 10 % 10 != 0:
            answer = result
            break
    task = f'Переведите дроби в проценты: {number}'
    return task, answer


def task_760():
    '''Генерация аналогичных задач № 760 с портала https://kuzovkin.info/one_exercise_1/760
    Переведите дроби в проценты: 0,063'''
    while True:
        number = round(np.random.uniform(0, 1), 3)
        if number * 10 % 10 == 0:
          continue
        result = number * 100
        if 0 <= result <= 99 and len(str(result)) <= 6 and result * 10 % 10 != 0:
            answer = result
            break
    task = f'Переведите дроби в проценты: {number}'
    return task, answer


def task_763():
    '''Генерация аналогичных задач № 763 с портала https://kuzovkin.info/one_exercise_1/763
    Переведите дроби в проценты: 1,01'''
    while True:
        number = round(np.random.uniform(1, 50), 3)
        if number * 10 % 10 == 0:
          continue
        result = number * 100
        if len(str(result)) <= 5 and result * 10 % 10 != 0:
            answer = result
            break
    task = f'Переведите дроби в проценты: {number}'
    return task, answer


def task_781():
    '''Генерация аналогичных задач № 781 с портала https://kuzovkin.info/one_exercise_1/781
    Переведите дроби в проценты: 1/3'''
    while True:
        number, number1 = np.random.randint(1, 50, size=2)
        result = (number / number1) * 100
        if len(str(result)) <= 5 and result * 10 % 10 != 0:
            answer = result
            break
    task = f'Переведите дроби в проценты: $\\frac{{{number}}}{{{number1}}}$'
    return task, answer


def task_794():
    '''Генерация аналогичных задач № 794 с портала https://kuzovkin.info/one_exercise_1/794
    В избирательном округе 25000 избирателей. На выборы пришли 57% избирателей.
    Сколько человек приняли участие в голосовании?'''
    value = np.random.choice(['избиратели', 'люди'])
    while True:
        number, number1 = np.random.randint(1000, 100000), np.random.randint(1, 100)
        result = (number * number1) / 100
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'В избирательном округе {number} {choosing_declension_form(value)}. На выборы пришли {number1}% {choosing_declension_form(value)}. Сколько человек приняли участие в голосовании?'
    return task, answer


def task_833():
    '''Генерация аналогичных задач № 833 с портала https://kuzovkin.info/one_exercise_1/833
    Мальчик Гриша прочитал в первый день 30% всей книги, во второй − 40% оставшейся части, а в третий − оставшиеся 105 страниц.
    Сколько всего страниц было в книге?'''
    book = np.random.choice(generate_context('./text_tasks/context.json', 'books'))
    name = np.random.choice(['Гриша', 'Коля', 'Ваня'])
    while True:
        number, number1, number2 = np.random.randint(1, 50), np.random.randint(1, 50), np.random.randint(100, 200)
        result = ((((number1 * number2) / (100 - number1) + number2) * number) / (100 - number)) + (number1 * number2) / (100 - number1) + number2
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'Мальчик {name} прочитал в первый день {number}% {choosing_declension_form(book)}, во второй − {number1}% оставшейся части, а в третий − оставшиеся {number2} страниц. Сколько всего страниц было в {choosing_declension_form(book, "loct")}?'
    return task, answer


def task_851():
    '''Генерация аналогичных задач № 851 с портала https://kuzovkin.info/one_exercise_1/851
    Цена на акцию сначала увеличилась на 1% процент, а потом уменьшилась на 1%.
    На сколько процентов и в какую сторону изменилась цена акции по сравнению с первоначальной?'''
    value = np.random.choice(['акция', 'товар'])
    while True:
        number, number1 = np.random.randint(1, 20, size=2)
        result = ((((100 + number) - ((100 + number) * (number1 / 100))) - 100) / 100) * 100
        if result * 10 % 10 != 0 and len(str(result)) <= 6:
            break
    task = f'Цена на {choosing_declension_form(value, "accs")} сначала увеличилась на {number}% процент, а потом уменьшилась на {number1}%. На сколько процентов и в какую сторону изменилась цена {choosing_declension_form(value)} по сравнению с первоначальной?'
    if result < 0:
        answer = f'уменьшилась на {abs(result)}'
        return task, answer
    else:
        answer = f'увеличилась на {result}'
        return task, answer


def task_855():
    '''Генерация аналогичных задач № 855 с портала https://kuzovkin.info/one_exercise_1/855
    Цена на проезд три раза увеличилась на 10%.
    На сколько процентов увеличилась цена по сравнению с первоначальной?'''
    value = np.random.choice(['два', 'четыре', 'три'])
    while True:
        number = np.random.randint(1, 100)

        if value == 'два':
            result = ((1 + (number / 100)) ** 2 - 1) * 100
        elif value == 'четыре':
            result = ((1 + (number / 100)) ** 4 - 1) * 100
        else:
            result = ((1 + (number / 100)) ** 3 - 1) * 100

        if len(str(result)) <= 8:
            break
    task = f'Цена на проезд {value} раза увеличилась на {number}%. На сколько процентов увеличилась цена по сравнению с первоначальной?'
    if result * 10 % 10 == 0:
        answer = int(result)
        return task, answer
    else:
        answer = result
        return task, answer


def task_870():
    '''Генерация аналогичных задач № 870 с портала https://kuzovkin.info/one_exercise_1/870
    Акционер компании “Математика Forever” решил уберечь деньги во время финансового кризиса и вложить их в какой-нибудь надёжный банк.
    Он выбрал ММБ − Московский Математический Банк (там работают только математики, так что банк очень надёжный).
    В ММБ есть много видов вкладов, но наш акционер остановил свой выбор на двух.
    А) Вклад на два года, 12% годовых, проценты выплачиваются в конце срока.
    Б) Вклад на два года, 11% годовых, проценты выплачиваются в конце каждого года и причисляются к сумме вклада (капитализация).
    Какую прибыль получит наш акционер, если положит 1000000000 рублей на первый вклад?'''
    value = np.random.choice(['два', 'три', 'четыре'])
    while True:
        number, number1 = np.random.randint(1, 20), np.random.randint(100000, 90000000)
        if number1 % 10000 != 0:
          continue

        if value == 'два':
            result = number1 * (number * 2 / 100)
        elif value == 'четыре':
            result = number1 * (number * 4 / 100)
        else:
            result = number1 * (number * 3 / 100)

        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'Акционер решил уберечь деньги и вложить их в банк. Где вклад на {value} года, {number}% годовых, проценты выплачиваются в конце срока. Какую прибыль получит акционер, если положит {number1} рублей?'
    return task, answer


def task_918():
    '''Генерация аналогичных задач № 918 с портала https://kuzovkin.info/one_exercise_1/918
    Колхоз засеял овсом 47 га, что составляет 37,6% всего участка, намеченного под овёс.
    Определить размеры этого участка.'''
    value = np.random.choice(['овёс', 'пшеница', 'рожь'])
    while True:
        number, number1 = np.random.randint(1, 100), round(np.random.uniform(1, 95), 2)
        if number1 * 10 % 10 == 0:
          continue
        result = number / (number1  / 100)
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'Колхоз засеял {choosing_declension_form(value, "ablt")} {number} га, что составляет {number1}% всего участка, намеченного под {choosing_declension_form(value, "accs")}. Определить размеры этого участка.'
    return task, answer


def task_925():
    '''Генерация аналогичных задач № 925 с портала https://kuzovkin.info/one_exercise_1/925
    Военные специалисты считали, что продвижение вперёд с боями на 15 км в сутки является пределом.
    Войска Советской Армии показали невиданно стремительный темп наступления, проходя летом 1944 г. с боями по 25 км в сутки.
    На сколько процентов были превзойдены Советской Армией нормы, считавшиеся предельными?'''
    while True:
        number, number1 = np.random.randint(10, 50, size=2)
        if number1 <= number:
          continue
        result = ((number1 - number) / number) * 100
        if result * 10 % 10 != 0 and len(str(result)) <= 6:
            answer = result
            break
    task = f'Военные специалисты считали, что продвижение вперёд с боями на {number} км в сутки является пределом. Войска показали невиданно стремительный темп наступления с боями по {number1} км в сутки. На сколько процентов были превзойдены войском нормы, считавшиеся предельными?'
    return task, answer


def task_4465():
    '''Генерация аналогичных задач № 4465 с портала https://kuzovkin.info/one_exercise_1/4465
    120 г золота сплавили с 80 г серебра.
    Найдите концентрацию золота и серебра в полученном сплаве.'''
    metal, metal_1 = random.sample(generate_context('./text_tasks/context.json', 'metals'), 2)
    while True:
        number, number1 = np.random.randint(10, 300), np.random.randint(10, 100)
        result, result1 = (number / (number + number1)) * 100, (number1 / (number + number1)) * 100
        if result * 10 % 10 == 0 and result1 * 10 % 10 == 0 :
            answer = f'{int(result)}:{int(result1)}'
            break
    task = f'{number} г {choosing_declension_form(metal)} сплавили с {number1} г {choosing_declension_form(metal_1)}. Найдите концентрацию {choosing_declension_form(metal)} и {choosing_declension_form(metal_1)} в полученном сплаве.'
    return task, answer


def task_4468():
    '''Генерация аналогичных задач № 4468 с портала https://kuzovkin.info/one_exercise_1/4468
    Концентрация серной кислоты в растворе составляет 22%.
    Сколько чистой серной кислоты и сколько воды содержится в 150 г раствора?'''
    acid = np.random.choice(generate_context('./text_tasks/context.json', 'acids'))
    while True:
        number, number1 = np.random.randint(1, 95), np.random.randint(10, 500)
        result, result1 = (number / 100) * number1, ((100 - number) / 100) * number1
        if result * 10 % 10 == 0 and result1 * 10 % 10 == 0 :
            answer = f'{int(result)}:{int(result1)}'
            break
    task = f'Концентрация {choosing_declension_form(acid)} кислоты в растворе составляет {number}%. Сколько чистой {choosing_declension_form(acid)} кислоты и сколько воды содержится в {number1} г раствора?'
    return task, answer


def task_4471():
    '''Генерация аналогичных задач № 4471 с портала https://kuzovkin.info/one_exercise_1/4471
    Сколько воды надо добавить к 30 г соли, чтобы получить пятипроцентный раствор соли?'''
    product = np.random.choice(generate_context('./text_tasks/context.json', 'products'))
    percent = np.random.choice(['пятипроцентный', 'четырехпроцентный', 'десятипроцентный'])
    while True:
        number = np.random.randint(1, 100)

        if percent == 'пятипроцентный':
            result = (number * 100 / 5) - number
        elif percent == 'четырехпроцентный':
            result = (number * 100 / 4) - number
        else:
            result = (number * 100 / 10) - number

        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'Сколько воды надо добавить к {number} г {choosing_declension_form(product)}, чтобы получить {percent} раствор {choosing_declension_form(product)}?'
    return task, answer


def task_4474():
    '''Генерация аналогичных задач № 4474 с портала https://kuzovkin.info/one_exercise_1/4474
    Сколько соли надо добавить к 190 г воды, чтобы получить пятипроцентный раствор соли?'''
    product = np.random.choice(generate_context('./text_tasks/context.json', 'products'))
    percent = np.random.choice(['пятипроцентный', 'четырехпроцентный', 'десятипроцентный'])
    while True:
        number = np.random.randint(100, 500)

        if percent == 'пятипроцентный':
            result = (5 * number) / (95)
        elif percent == 'четырехпроцентный':
            result = (4 * number) / (96)
        else:
            result = (10 * number) / (90)

        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'Сколько {choosing_declension_form(product)} надо добавить к {number} г воды, чтобы получить {percent} раствор {choosing_declension_form(product)}?'
    return task, answer


def task_4488():
    '''Генерация аналогичных задач № 4488 с портала https://kuzovkin.info/one_exercise_1/4488
    Стоимость покупки с учётом четырёхпроцентной скидки по дисконтной карте составила 1152 рубля.
    Сколько рублей пришлось бы заплатить за покупку при отсутствии дисконтной карты?'''
    percent = np.random.choice(['пятипроцентной', 'четырёхпроцентной', 'десятипроцентной'])
    value = np.random.choice(['товар', 'покупка', 'продукт'])
    while True:
        number = np.random.randint(1000, 100000)

        if percent == 'пятипроцентной':
            result = number / (95 / 100)
        elif percent == 'четырёхпроцентной':
            result = number / (96 / 100)
        else:
            result = number / (90 / 100)

        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'Стоимость {choosing_declension_form(value)} с учётом {percent} скидки по дисконтной карте составила {number} рубля. Сколько рублей пришлось бы заплатить за {choosing_declension_form(value, "accs")} при отсутствии дисконтной карты?'
    return task, answer


def task_4497():
    '''Генерация аналогичных задач № 4497 с портала https://kuzovkin.info/one_exercise_1/4497
    В первом квартале доля рынка, занимаемая товарами отечественных производителей, увеличилась с 20% до 25% процентов, а во втором − с 25% до 30%.
    На сколько процентов увеличилась отечественная доля рынка во 2 квартале?'''
    product = np.random.choice(generate_context('./text_tasks/context.json', 'goods'))
    while True:
        number, number1, number2 = np.random.randint(1, 95, size=3)
        if number >= number1 or number1 >= number2:
          continue
        result = number2 - number1
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'В первом квартале доля рынка, занимаемая {choosing_declension_form(product, "ablt")} товарами, увеличилась с {number}% до {number1}% процентов, а во втором − с {number1}% до {number2}%. На сколько процентов увеличилась доля рынка во 2 квартале?'
    return task, answer


def task_4498():
    '''Генерация аналогичных задач № 4498 с портала https://kuzovkin.info/one_exercise_1/4498
    В первом квартале доля рынка, занимаемая товарами отечественных производителей, увеличилась с 20% до 25% процентов, а во втором − с 25% до 30%.
    В каком квартале увеличение было более значительным(в ответ написать разность процентов между первым и вторым)?'''
    product = np.random.choice(generate_context('./text_tasks/context.json', 'goods'))
    while True:
        number, number1, number2 = np.random.randint(1, 95, size=3)
        if number >= number1 or number1 >= number2:
          continue
        result = (number1 - number) - (number2 - number1)
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'В первом квартале доля рынка, занимаемая {choosing_declension_form(product, "ablt")} товарами, увеличилась с {number}% до {number1}% процентов, а во втором − с {number1}% до {number2}%. В каком квартале увеличение было более значительным(в ответ написать разность процентов между первым и вторым)?'
    return task, answer


def task_4501():
    '''Генерация аналогичных задач № 4501 с портала https://kuzovkin.info/one_exercise_1/4501
    Кофе при обжаривании теряет 12,5% своего веса.
    Сколько килограммов свежего кофе нужно взять, чтобы получить 42 кг жареного?'''
    product = np.random.choice(['банан', 'виноград', 'абрикос'])
    while True:
        percent = round(np.random.uniform(60, 85), 2)
        number = np.random.randint(1, 100)
        if percent * 10 % 10 == 0:
          continue
        result = number / ((100 - percent) / 100)
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'{product.capitalize()} при сушки теряет {percent}% своего веса. Сколько килограммов {choosing_declension_form(product)} нужно взять, чтобы получить {number} кг сушеного?'
    return task, answer


def task_4510():
    '''Генерация аналогичных задач № 4510 с портала https://kuzovkin.info/one_exercise_1/4510
    Туристы проехали 50% пути на поезде и 40% пути на автобусе. Какую часть пути осталось пройти туристам?'''
    value = np.random.choice(['люди', 'туристы', 'пассажиры'])
    while True:
        number, number1 = np.random.randint(10, 100, size=2)
        if number + number1 >= 100:
          continue
        result = 100 - (number + number1)
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'{value.capitalize()} проехали {number}% пути на поезде и {number1}% пути на автобусе. Какую часть пути осталось пройти {choosing_declension_form(value, "datv")}?'
    return task, answer


def task_4512():
    '''Генерация аналогичных задач № 4512 с портала https://kuzovkin.info/one_exercise_1/4512
    Сплав меди, цинка и олова содержит 20% меди и 45% цинка. Сколько в этом сплаве олова?'''
    metal, metal_1, metal_2 = random.sample(generate_context('./text_tasks/context.json', 'metals'), 3)
    while True:
        number, number1 = np.random.randint(10, 100, size=2)
        if number + number1 >= 100:
          continue
        result = 100 - (number + number1)
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'Сплав {choosing_declension_form(metal)}, {choosing_declension_form(metal_1)} и {choosing_declension_form(metal_2)} содержит {number}% {choosing_declension_form(metal)} и {number1}% {choosing_declension_form(metal_1)}. Сколько в этом сплаве {choosing_declension_form(metal_2)}?'
    return task, answer


def task_4517():
    '''Генерация аналогичных задач № 4517 с портала https://kuzovkin.info/one_exercise_1/4517
    Основным материалом при изготовлении самолётов является сплав дюралюминий (другие названия − дуралюмин, дюраль).
    Дюралюминий − самый прочный сплав среди сплавов на основе алюминия.
    Кроме алюминия, дюралюминий содержит медь (1,4%), магний (0,4%), марганец (1%), кремний (0,5%), цинк (7%), железо (1,8%) и титан (0,35%).
    Сколько в таком сплаве процентов алюминия?'''
    metal, metal_1, metal_2, metal_3, metal_4, metal_5, metal_6, metal_7 = random.sample(generate_context('./text_tasks/context.json', 'metals'), 8)
    while True:
        number, number1, number2, number3, number4, number5, number6 = np.round(np.random.uniform(0, 10, size=7), 2)
        numbers_list = [number, number1, number2, number3, number4, number5 ,number6]
        for i in numbers_list:
          if i * 10 % 10 == 0:
            continue
        result = 100 - (number + number1 + number2 + number3 + number4 + number5 + number6)
        if result * 10 % 10 != 0 and len(str(result)) <= 5:
            answer = result
            break
    task = f'Сплав, кроме {choosing_declension_form(metal)}, содержит {choosing_declension_form(metal_1, "accs")} ({number}%), {choosing_declension_form(metal_2, "accs")} ({number1}%), {choosing_declension_form(metal_3, "accs")} ({number2}%), {choosing_declension_form(metal_4, "accs")} ({number3}%), {choosing_declension_form(metal_5, "accs")} ({number4}%), {choosing_declension_form(metal_6, "accs")} ({number5}%) и {choosing_declension_form(metal_7, "accs")} ({number6}%). Сколько в таком сплаве процентов {choosing_declension_form(metal)}?'
    return task, answer


def task_4521():
    '''Генерация аналогичных задач № 4521 с портала https://kuzovkin.info/one_exercise_1/4521
    Который теперь час, если остающаяся часть суток равна 60% протекшей части?'''
    while True:
        number = np.random.randint(1, 100)
        total = 86400 / (1 + number / 100)
        if total * 10 % 10 != 0:
          continue
        hours = int(total / 3600)
        minutes = int(total / 60) - (hours * 60)
        seconds = int(total % 60)

        if hours <= 9:
            hours = f'0{hours}'
        if minutes <= 9:
            minutes = f'0{minutes}'
        if seconds <= 9:
            seconds = f'0{seconds}'

        answer = f'{hours}:{minutes}:{seconds}'
        break
    task = f'Который теперь час, если остающаяся часть суток равна {number}% протекшей части?'
    return task, answer


def task_4526():
    '''Генерация аналогичных задач № 4526 с портала https://kuzovkin.info/one_exercise_1/4526
    Найдите: 34,1% от 1010'''
    while True:
        number, number1 = round(np.random.uniform(1, 99), 2), np.random.randint(1000, 10000)
        if number * 10 % 10 == 0:
          continue
        result = number1 * (number / 100)
        if len(str(result)) <= 5 and result * 10 % 10 != 0:
            answer = result
            break
    task = f'Найдите: {number}% от {number1}'
    return task, answer


def task_4535():
    '''Генерация аналогичных задач № 4535 с портала https://kuzovkin.info/one_exercise_1/4535
    Найдите: 0,4% от 55'''
    while True:
        number, number1 = round(np.random.uniform(0, 1), 2), np.random.randint(10, 100)
        if number * 10 % 10 == 0:
          continue
        result = number1 * (number / 100)
        if len(str(result)) <= 5 and result * 10 % 10 != 0:
            answer = result
            break
    task = f'Найдите: {number}% от {number1}'
    return task, answer


def task_4542():
    '''Генерация аналогичных задач № 4542 с портала https://kuzovkin.info/one_exercise_1/4542
    Найдите: 13,4% от 180'''
    while True:
        number, number1 = round(np.random.uniform(10, 99), 2), np.random.randint(100, 1000)
        if number * 10 % 10 == 0:
          continue
        result = number1 * (number / 100)
        if len(str(result)) <= 5 and result * 10 % 10 != 0:
            answer = result
            break
    task = f'Найдите: {number}% от {number1}'
    return task, answer


def task_4543():
    '''Генерация аналогичных задач № 4543 с портала https://kuzovkin.info/one_exercise_1/4543
    Найдите: 0,5% от 12'''
    while True:
        number, number1 = round(np.random.uniform(0, 1), 2), np.random.randint(1, 100)
        if number * 10 % 10 == 0:
          continue
        result = number1 * (number / 100)
        if len(str(result)) <= 5 and result * 10 % 10 != 0:
            answer = result
            break
    task = f'Найдите: {number}% от {number1}'
    return task, answer


def task_4547():
    '''Генерация аналогичных задач № 4547 с портала https://kuzovkin.info/one_exercise_1/4547
    Найдите: 9,75% от 540'''
    while True:
        number, number1 = round(np.random.uniform(10, 99), 2), np.random.randint(100, 1000)
        if number * 10 % 10 == 0:
          continue
        result = number1 * (number / 100)
        if len(str(result)) <= 5 and result * 10 % 10 != 0:
            answer = result
            break
    task = f'Найдите: {number}% от {number1}'
    return task, answer


def task_4551():
    '''Генерация аналогичных задач № 4551 с портала https://kuzovkin.info/one_exercise_1/4551
    Найдите: 7,45% от 56,2'''
    while True:
        number, number1 = np.round(np.random.uniform(1, 99, size=2), 2)
        if number * 10 % 10 == 0 or number1 * 10 % 10 == 0:
          continue
        result = number1 * (number / 100)
        if len(str(result)) <= 5 and result * 10 % 10 != 0:
            answer = result
            break
    task = f'Найдите: {number}% от {number1}'
    return task, answer


def task_4556():
    '''Генерация аналогичных задач № 4556 с портала https://kuzovkin.info/one_exercise_1/4556
    Найдите целое, если 15% равны 45'''
    while True:
        number, number1 = np.random.randint(10, 99, size=2)
        result = number1 / (number / 100)
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'Найдите целое, если {number}% равны {number1}'
    return task, answer


def task_4557():
    '''Генерация аналогичных задач № 4557 с портала https://kuzovkin.info/one_exercise_1/4557
    Найдите целое, если 19% равны 57'''
    while True:
        number, number1 = np.random.randint(10, 99, size=2)
        result = number1 / (number / 100)
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'Найдите целое, если {number}% равны {number1}'
    return task, answer


def task_4559():
    '''Генерация аналогичных задач № 4559 с портала https://kuzovkin.info/one_exercise_1/4559
    Найдите целое, если 35% равны 105'''
    while True:
        number, number1 = np.random.randint(10, 99), np.random.randint(100, 1000)
        result = number1 / (number / 100)
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'Найдите целое, если {number}% равны {number1}'
    return task, answer


def task_4562():
    '''Генерация аналогичных задач № 4562 с портала https://kuzovkin.info/one_exercise_1/4562
    Найдите целое, если 120% равны 360'''
    while True:
        number, number1 = np.random.randint(100, 1000, size=2)
        result = number1 / (number / 100)
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'Найдите целое, если {number}% равны {number1}'
    return task, answer


def task_4564():
    '''Генерация аналогичных задач № 4564 с портала https://kuzovkin.info/one_exercise_1/4564
    Найдите целое, если 5% равны 2,5'''
    while True:
        number, number1 = np.random.randint(1, 100), round(np.random.uniform(1, 10), 2)
        if number1 * 10 % 10 == 0:
          continue
        result = number1 / (number / 100)
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'Найдите целое, если {number}% равны {number1}'
    return task, answer


def task_4565():
    '''Генерация аналогичных задач № 4565 с портала https://kuzovkin.info/one_exercise_1/4565
    Найдите целое, если 7% равны 0,77'''
    while True:
        number, number1 = np.random.randint(1, 100), round(np.random.uniform(0, 1), 2)
        if number1 * 10 % 10 == 0:
          continue
        result = number1 / (number / 100)
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'Найдите целое, если {number}% равны {number1}'
    return task, answer


def task_4566():
    '''Генерация аналогичных задач № 4566 с портала https://kuzovkin.info/one_exercise_1/4566
    Найдите целое, если 15% равны 6'''
    while True:
        number, number1 = np.random.randint(1, 100, size=2)
        if number == number1:
          continue
        result = number1 / (number / 100)
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'Найдите целое, если {number}% равны {number1}'
    return task, answer


def task_4568():
    '''Генерация аналогичных задач № 4568 с портала https://kuzovkin.info/one_exercise_1/4568
    Найдите целое, если 18% равны 27'''
    while True:
        number, number1 = np.random.randint(1, 100, size=2)
        if number == number1:
          continue
        result = number1 / (number / 100)
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'Найдите целое, если {number}% равны {number1}'
    return task, answer


def task_4571():
    '''Генерация аналогичных задач № 4571 с портала https://kuzovkin.info/one_exercise_1/4571
    Найдите целое, если 5,05% равны 161,6'''
    while True:
        number, number1 = round(np.random.uniform(1, 10), 2), round(np.random.uniform(100, 1000), 2)
        if number * 10 % 10 == 0 or number1 * 10 % 10 == 0:
          continue
        result = number1 / (number / 100)
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'Найдите целое, если {number}% равны {number1}'
    return task, answer


def task_4574():
    '''Генерация аналогичных задач № 4574 с портала https://kuzovkin.info/one_exercise_1/4574
    Найдите целое, если 99,9% равны 25174,8'''
    while True:
        number, number1 = round(np.random.uniform(10, 100), 2), round(np.random.uniform(1000, 100000), 2)
        if number * 10 % 10 == 0 or number1 * 10 % 10 == 0:
          continue
        result = number1 / (number / 100)
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'Найдите целое, если {number}% равны {number1}'
    return task, answer


def task_4575():
    '''Генерация аналогичных задач № 4575 с портала https://kuzovkin.info/one_exercise_1/4575
    Найдите целое, если 5,7% равны 57'''
    while True:
        number, number1 = round(np.random.uniform(1, 100), 2), np.random.randint(1, 100)
        if number * 10 % 10 == 0:
          continue
        result = number1 / (number / 100)
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'Найдите целое, если {number}% равны {number1}'
    return task, answer


def task_4576():
    '''Генерация аналогичных задач № 4576 с портала https://kuzovkin.info/one_exercise_1/4576
    Найдите целое, если 5% равны 3 1/3'''
    while True:
        number = np.random.randint(1, 100)
        number1, number2, number3 = np.random.randint(1, 20, size=3)
        if number2 >= number3:
          continue
        fract = number1 + (number2 / number3)
        result = fract / (number / 100)
        if result * 10 % 10 != 0 and len(str(result)) <= 4:
            answer = fraction_latex_format(result)
            break
    task = f'Найдите целое, если {number}% равны ${number1}\\frac{{{number2}}}{{{number3}}}$'
    return task, answer


def task_4579():
    '''Генерация аналогичных задач № 4579 с портала https://kuzovkin.info/one_exercise_1/4579
    Найдите целое, если 0,2% равны 2'''
    while True:
        number, number1 = round(np.random.uniform(0, 1), 2), np.random.randint(1, 100)
        if number * 10 % 10 == 0:
          continue
        result = number1 / (number / 100)
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'Найдите целое, если {number}% равны {number1}'
    return task, answer


def task_4581():
    '''Генерация аналогичных задач № 4581 с портала https://kuzovkin.info/one_exercise_1/4581
    Найдите целое, если 0,001% равны 57'''
    while True:
        number, number1 = round(np.random.uniform(0, 1), 4), np.random.randint(1, 100)
        if number * 10 % 10 == 0:
          continue
        result = number1 / (number / 100)
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'Найдите целое, если {number}% равны {number1}'
    return task, answer


def task_4583():
    '''Генерация аналогичных задач № 4583 с портала https://kuzovkin.info/one_exercise_1/4583
    В библиотеке 98000 книг. Книги на русском языке составляют 78% всех книг, из них 5% − учебники.
    Сколько учебников на русском языке в библиотеке?'''
    value = choosing_declension_form(np.random.choice(generate_context('./text_tasks/context.json', 'books')), "plur")
    if value == "книги":
        value = value = choosing_declension_form(np.random.choice(generate_context('./text_tasks/context.json', 'books')), "plur")
    while True:
        book, percent, percent_1 = np.random.randint(10000, 99999), np.random.randint(45, 80), np.random.randint(1, 20)
        if percent + percent_1 >= 100:
          continue
        result = (((book * percent) / 100) * percent_1) / 100
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'В библиотеке {book} книг. Книги на русском языке составляют {percent}% всех книг, из них {percent_1}% − {value}. Сколько {choosing_declension_form(value)} на русском языке в библиотеке?'
    return task, answer


def task_4587():
    '''Генерация аналогичных задач № 4587 с портала https://kuzovkin.info/one_exercise_1/4587
    За год число книг в библиотеке увеличилось на 10% и стало равным 8800.
    Сколько книг было в библиотеке в прошлом году?'''
    value = choosing_declension_form(np.random.choice(generate_context('./text_tasks/context.json', 'books')), "plur")
    if value == "книги":
        value = "книг"
    while True:
        book, percent = np.random.randint(1000, 9999), np.random.randint(1, 50)
        result = (book * 100) / (100 + percent)
        if result * 10 % 10 == 0:
            answer = int(result)
            break
    task = f'За год число {choosing_declension_form(value)} в библиотеке увеличилось на {percent}% и стало равным {book}. Сколько {choosing_declension_form(value)} было в библиотеке в прошлом году?'
    return task, answer


def task_4592():
    '''Генерация аналогичных задач № 4592 с портала https://kuzovkin.info/one_exercise_1/4592
    При перегонке нефти получается 30% керосина и 53% мазута, остальное – потери при переработке.
    Сколько керосина и мазута получится из 64 т нефти?'''
    product, product_1 = random.sample(generate_context('./text_tasks/context.json', 'hydrocarbon_products'), 2)
    while True:
        tone, percent, percent_1 = np.random.randint(10, 100, size=3)
        if percent + percent_1 >= 90:
          continue
        result = (tone * percent) / 100
        result_1 = (tone * percent_1) / 100
        if result * 10 % 10 != 0 and result_1 * 10 % 10 != 0:
            answer = f'{result}:{result_1}'
            break
    task = f'Из вещества получается {percent}% {choosing_declension_form(product)} и {percent_1}% {choosing_declension_form(product_1)}, остальное – потери. Сколько {choosing_declension_form(product)} и {choosing_declension_form(product_1)} получится из {tone} т вещества?'
    return task, answer


def task_4603():
    '''Генерация аналогичных задач № 4603 с портала https://kuzovkin.info/one_exercise_1/4603
    Переведите проценты в десятичную дробь: 0,009%'''
    while True:
        number = round(np.random.uniform(0, 1), 4)
        if number * 10 % 10 == 0:
          continue
        result = number / 100
        if len(str(result)) <= 6:
            answer = result
            break
    task = f'Переведите проценты в десятичную дробь: {number}'
    return task, answer


def task_4604():
    '''Генерация аналогичных задач № 4604 с портала https://kuzovkin.info/one_exercise_1/4604
    Переведите проценты в десятичную дробь: 133%'''
    while True:
        number = np.random.randint(100, 1000)
        result = number / 100
        if result % 1 != 0:
            answer = result
            break
    task = f'Переведите проценты в десятичную дробь: {number}%'
    return task, answer


def task_4607():
    '''Генерация аналогичных задач № 4607 с портала https://kuzovkin.info/one_exercise_1/4607
    Переведите проценты в десятичную дробь: 200%'''
    while True:
        number = np.random.randint(100, 1000)
        result = number / 100
        if result % 1 == 0:
            answer = int(result)
            break
        if result % 1 != 0:
            answer = result
            break
    task = f'Переведите проценты в десятичную дробь: {number}%'
    return task, answer


def task_4608():
    '''Генерация аналогичных задач № 4608 с портала https://kuzovkin.info/one_exercise_1/4608
    Переведите проценты в десятичную дробь: 1000%'''
    while True:
        number = np.random.randint(1000, 10000)
        result = number / 100
        if result % 1 == 0:
            answer = int(result)
            break
        if result % 1 != 0:
            answer = result
            break
    task = f'Переведите проценты в десятичную дробь: {number}%'
    return task, answer


def task_4612():
    '''Генерация аналогичных задач № 4612 с портала https://kuzovkin.info/one_exercise_1/4612
    Переведите проценты в десятичную дробь: 33 1/3 %'''
    while True:
        number, number1, number2 = np.random.randint(1, 50, size=3)
        if number1 % number2 == 0 or number1 >= number2:
          continue
        result = (number + (number1 / number2)) / 100
        if result % 1 != 0 and len(str(result)) <= 6:
            answer = result
            break
    task = f'Переведите проценты в десятичную дробь: ${number}\\frac{{{number1}}}{{{number2}}}$%'
    return task, answer


def task_4615():
    '''Генерация аналогичных задач № 4615 с портала https://kuzovkin.info/one_exercise_1/4615
    Переведите проценты в десятичную дробь: 5/7 %'''
    while True:
        number, number1 = np.random.randint(1, 50, size=2)
        if number % number1 == 0 or number >= number1:
          continue
        result = (number / number1) / 100
        if result % 1 != 0 and len(str(result)) <= 6:
            answer = result
            break
    task = f'Переведите проценты в десятичную дробь: $\\frac{{{number}}}{{{number1}}}$%'
    return task, answer


def task_4620():
    '''Генерация аналогичных задач № 4620 с портала https://kuzovkin.info/one_exercise_1/4620
    Переведите проценты в десятичную дробь: 8,75%'''
    while True:
        number = round(np.random.uniform(1, 20), 4)
        if number % 1 == 0:
          continue
        result = number / 100
        if result % 1 != 0 and len(str(result)) <= 6:
            answer = result
            break
    task = f'Переведите проценты в десятичную дробь: {number}%'
    return task, answer


def task_4622():
    '''Генерация аналогичных задач № 4622 с портала https://kuzovkin.info/one_exercise_1/4622
    Переведите проценты в десятичную дробь: 875%'''
    while True:
        number = np.random.randint(100, 1000)
        result = number / 100
        if result % 1 != 0 and len(str(result)) <= 4:
            answer = result
            break
    task = f'Переведите проценты в десятичную дробь: {number}%'
    return task, answer