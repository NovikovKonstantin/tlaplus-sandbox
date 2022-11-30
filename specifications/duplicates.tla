----------------------------- MODULE duplicates -----------------------------

EXTENDS Integers, Sequences, TLC, FiniteSets

S == 1..10

(*--algorithm duplicates

    variable
        seq \in S \X S \X S \X S; (*Массивы со всеми комбинациями цифр 1..10.*)
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
        (*ВАЖНО: Решение неточное и введено сейчас для построения рабочего кода.*)
        (*В будущем оно будет заменено.*)
        IsUnique(s) == 
            /\ Cardinality(seen) = Len(s)
            
        (*Инвариант проверяет корректность алгоритма после его завершения.*)
        IsCorrect == 
            /\ pc = "Done" (*Переходим к следующему шагу только если программа завершила свою работу.*)
            => is_unique = IsUnique(seq)
            
    end define;

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
    end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "8ced01e0" /\ chksum(tla) = "92158502")
VARIABLES seq, index, seen, is_unique, pc

(* define statement *)
TypeInvariant ==

    /\ is_unique \in BOOLEAN

    /\ seen \subseteq S

    /\ index \in 1..Len(seq)+1




IsUnique(s) ==
    /\ Cardinality(seen) = Len(s)


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
                 ELSE /\ pc' = "Done"
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
