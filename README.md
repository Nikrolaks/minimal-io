Тут есть некоторые [мысли по курсовой](https://docs.google.com/document/d/1xjLKAkinbv5_SlKIQW87ZD2QaNcFBvBcb8TS5rksiNM/edit?usp=sharing)

Я их пишу в свободной форме, чтобы у меня было, что написать в отчете потом ну и чтобы было, что рассказать на защите, что написать в презентации.

# show-minimal

Судя по всему, основная работа закончена, осталось только подчистить, убедиться, что я точно все базовые "кирпичики" разобрала (точно нет, потому что я не учитываю тип void)

А еще нужно найти, какой же флаг мне позволит, имея реализацию на дженериках, сделать свой класс derivable

А еще нужно написать красивый, хороший README :)

# read-minimal

Я внезапно вспомнила, что моя курсовая заключалась не только в том, чтобы написать писателя, но и сделать читателя.

Спохватилась и оказалось, что писать читателя даже проще, кроме одного жирнющего НО

А ГдЕ МНе вЗяТЬ пРедСТаВИтЕЛя, еСлИ я ДолЖНа ЕгО сГенЕРирОвАТь??
Мне же нужен был представитель для того, чтобы вынуть конструктор, его фиксность, селектор он или нет...
Таким образом, пока у меня реализация с очень грубым хаком - в качестве представителя я даю ему undefined...

Функции, которые вынимают мне мету, не пользуются представителем, они пользуются его типом. Благодаря ленивости, я не натыкаюсь на undefined там, где мне приходится использовать unM1, чтобы получить представителя внутреннего типа.

Есть только идея, что можно как-то через let сделать, но это все равно будет выглядеть как хак! Пока нет мыслей, как бы сделать это по-нормальному.

Пока что опять не работают случаи с держанием более сложных типов, как было в писателе, который не ставил скобки, но, думаю, я с этим разберусь.
