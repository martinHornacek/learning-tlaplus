-------------------------------- MODULE spa --------------------------------
EXTENDS Naturals

CONSTANT max_num_q

VARIABLE num, count_right, count_wrong, result, input_enabled, check_enabled, new_question_enabled

vars == << num, count_right, count_wrong, result, input_enabled, check_enabled, new_question_enabled >>

Init == /\ num = 1
        /\ count_right = 0
        /\ count_wrong = 0
        /\ input_enabled = TRUE
        /\ check_enabled = FALSE
        /\ new_question_enabled = FALSE
        /\ result = ""

Input_Answer == /\ input_enabled = TRUE
                /\ input_enabled' = FALSE
                /\ check_enabled' = TRUE
                /\ UNCHANGED << num, count_right, count_wrong, new_question_enabled, result >>
                
Check == /\ check_enabled = TRUE
         /\ check_enabled' = FALSE
         /\ new_question_enabled' = TRUE
         /\ \E answer_correct \in { TRUE, FALSE } : IF answer_correct = TRUE THEN
                                                        /\ count_right' = count_right + 1
                                                        /\ result' = "Right"
                                                        /\ UNCHANGED count_wrong
                                                    ELSE /\ count_wrong' = count_wrong + 1
                                                         /\ UNCHANGED count_right
                                                         /\ result' = "Wrong"
         /\ UNCHANGED << num, input_enabled >>
         
New_Question == /\ num < max_num_q
                /\ new_question_enabled = TRUE
                /\ new_question_enabled' = FALSE
                /\ num' = num + 1
                /\ input_enabled' = TRUE
                /\ result' = ""
                /\ UNCHANGED << count_right, count_wrong, check_enabled >>
                
               
Terminating == /\ num = max_num_q
               /\ UNCHANGED vars        
              
Next == \/ Input_Answer
        \/ Check
        \/ New_Question
        \/ Terminating
        
Spec == Init /\ [][Next]_vars/\WF_vars(Next)
=============================================================================
\* Modification History
\* Last modified Tue Jan 17 19:47:09 CET 2023 by martin
\* Created Tue Jan 17 19:33:50 CET 2023 by martin
