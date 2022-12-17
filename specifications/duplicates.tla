----------------------------- MODULE duplicates -----------------------------

EXTENDS Integers, Sequences, TLC, FiniteSets

(*S задается в каждой модели отдельно.*)
(*Делаем модель чище, убирая из нее хардкодные элементы.*)
CONSTANT S, DEBUG

(*Обязательная проверка, что в S есть достаточное количество разных элементов, которое вообще имеет смысл оценивать моделью.*)
ASSUME Cardinality(S) >= 4
ASSUME DEBUG \in BOOLEAN

(*--algorithm duplicates
    
    variable
        seq \in S \X S \X S \X S; (*Массивы со всеми комбинациями элементов S.*)
        index = 1;
        seen = {};
        is_unique = TRUE;

    (*Объявляем операторы на чистом TLA+ посреди Pluscal-кода.*)
    define
        (*Инвариант проверяет, что все значения не выходят за пределы диапазонов допустимых значений.*)
        TypeInvariant ==
            (*Проверяем, что is_unique типа BOOLEAN.*)
            /\ is_unique \in BOOLEAN
            (*Проверяем, что seen содержит только элементы S.*)
            /\ seen \subseteq S
            (*Проверяем, что за время работы программы мы выйдем за пределы массива только один раз (и закончим на этом работу).*)
            /\ index \in 1..Len(seq)+1
 
        (*Инвариант проверяет, что в seq есть/отсутствуют дубликаты.*)
        IsUnique(s) == 
            \A i, j \in 1..Len(s): (* Перебираем все комбинации i и j.*)
                (*Для всех i != j должно быть истинным seg[i] != seg[j].*)
                (*Оператор # - это односимвольный эквивалент /= (не равно).*)
                (*Вывод ниже можно записать как i /= j => seq /= seq[j].*)
                i # j => seq[i] # seq[j]
            
        (*Инвариант проверяет корректность алгоритма после его завершения.*)
        IsCorrect == 
            /\ pc = "Done" (*Переходим к следующему шагу только если программа завершила свою работу.*)
            => is_unique = IsUnique(seq)
            
    end define;

    (*Debug-процедура, которую можно использовать для вывода текста при debug'e.*)
    (*Такие процедуры должны быть помещены внутри Pluscal-блока над begin-секцией алгоритма.*)
    macro print_if_debug(str) begin
        if DEBUG then
            print str
        end if;
    end macro;
    
    begin
      Iterate:
        while index <= Len(seq) do
          if seq[index] \notin seen then
            seen := seen \union {seq[index]};
          else
            is_unique := FALSE;
          end if;
          index := index + 1;
        end while;
        print_if_debug("End Iterate");
        
    end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "fb0bc55d" /\ chksum(tla) = "3f43d78e")
VARIABLES seq, index, seen, is_unique, pc

(* define statement *)
TypeInvariant ==

    /\ is_unique \in BOOLEAN

    /\ seen \subseteq S

    /\ index \in 1..Len(seq)+1


IsUnique(s) ==
    \A i, j \in 1..Len(s):



        i # j => seq[i] # seq[j]


IsCorrect ==
    /\ pc = "Done"
    => is_unique = IsUnique(seq)


vars == << seq, index, seen, is_unique, pc >>

Init == (* Global variables *)
        /\ seq \in S \X S \X S \X S
        /\ index = 1
        /\ seen = {}
        /\ is_unique = TRUE
        /\ pc = "Iterate"

Iterate == /\ pc = "Iterate"
           /\ IF index <= Len(seq)
                 THEN /\ IF seq[index] \notin seen
                            THEN /\ seen' = (seen \union {seq[index]})
                                 /\ UNCHANGED is_unique
                            ELSE /\ is_unique' = FALSE
                                 /\ seen' = seen
                      /\ index' = index + 1
                      /\ pc' = "Iterate"
                 ELSE /\ IF DEBUG
                            THEN /\ PrintT("End Iterate")
                            ELSE /\ TRUE
                      /\ pc' = "Done"
                      /\ UNCHANGED << index, seen, is_unique >>
           /\ seq' = seq

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Iterate
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
