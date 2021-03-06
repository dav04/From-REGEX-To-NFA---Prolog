Progetto Prolog:
"Compilazione d'espressioni regolari in automi non deterministici"

Lo scopo del progetto è quella di implementare un compilatore che trasforma un'espressione regolare in un atoma NFA.
Di seguito si da una definizione di espressione regolare, così da avere un'idea chiara su che cosa sia e come viene definita in Prolog, 
si elencano gli operatori principali e tutti i predicati che compongono il programma; 
inoltre si mostra la struttura principale degli automi dei vari operatori.

--------------------------------
DEFINIZIONE ESPRESSIONE REGOLARE
--------------------------------
Si definisce espressione regolare:

1 - a, cioè qualsiasi simbolo che formano un alfabeto Σ

2 - ε, cioè una stringa vuota (in Prolog [epsilon])

3 - Ø, cioè l'insieme vuoto (in Prolog [])

4 - RE1 U RE2 (in Prolog operatori alt e oneof)

5 - RE1 ° RE2 (in Prolog operatore seq)

6 - RE* (in Prolog operatori star (0 o più) e plus (1 o più))

--------------------------------
OPERATORI ESPRESSIONI REGOLARI
--------------------------------
- seq	(<RE1>, <RE2>, <RE3>, ....)	sequenza di espressioni regolari
- star	(<RE>)				( )*  0 o più espressioni regolari
- plus	(<RE>)				( )*  1 o più espressioni regolari
- bar	(<RE>)				negazione dell'espressione regolare
- alt	(<RE1>, <RE2>, <RE3>, ....)	alternanza espressioni regolari
- oneof	(s1, s2, s3, ...)		alternanza di soli simboli

--------------------------------
PREDICATI PUBBLICI
--------------------------------
- is_regexp/1			(RE)						verifica che RE sia un'espressione regolare
- nfa_compile_regexp/2		(FA_Id, RE)					crea e inserisce nella base di dati l'automa
- nfa_recognize/2		(FA_Id, Input)					riconosce linguaggio attraverso l'automa; Input è una lista
- nfa_clear/0									pulisce la base di dati
- nfa_clear/1			(FA_Id)						pulisce la base di dati eliminando l'automa selezionato
- nfa_list/0									visualizza l'attuale base di dati
- nfa_list/1			(FA_Id)						visualizza l'automa selezionato presente nella base di dati

--------------------------------
PREDICATI PRIVATI
--------------------------------
- nfa_delta/4			(FA_Id, Stato1, Input, Stato2)			stati intermedi dell'automa
- nfa_initial/2			(FA_Id, Stato)					stato iniziale di un automa
- nfa_final/2			(FA_Id, Stato)					stato finale di un atoma
- is_regexp_list/1		(REX)						verifica che REX sia un'espressione regolare
- is_operator/2			(OP, REX)					verifica che OP sia un operatore corretto
- split_regexp/3		(RE, OP, REX)					suddivide RE in due liste: operatori (OP) ed espressioni regolari (REX)
- regexp_op_list/6		(FA_Id, OP, REX, Initial, Final, Final2)	crea l'automa che non ha operatori oppure indirizza gli operatori a regexp_op
- regexp_op/5			(FA_Id, OP, REX, Initial, Final)		crea l'automa in base all'operatore OP ottenuto
- regexp_op_bar/6		(FA_Id, [OP, bar], REX, Initial, Final, Final2)	crea l'automa di un operatore preceduto da bar
- find_delta_star/3		(FA_Id, Q, Initial)				crea epsilon mosse dalla listadi stati Q allo stato iniziale
- find_delta_plus/3		(FA_Id, Q, Initial)				crea epsilon mosse dalla listadi stati Q allo stato iniziale
- find_delta_bar_seq/4		(FA_Id, Initial, N_State, Final)		in caso di bar(seq(...)) collega ogni stato della sequenza allo stato finale	
- find_delta_bar_alt/3		(FA_Id, Q, Final)				in caso di bar(alt(...)) collega gli ultimi stati allo stato finale
- nfa_recognize_accept/3 	(FA_Id, Input, State)				"attraversa" l'automa fino a raggiungere e verificare lo stato finale

Gestione eccezione degli errori:
- check_id/1			(FA_Id)		"id non corretto"		verifica che FA_Id non sia una variabile
- check_id_exists/1		(FA_Id)		"id già presente"		verifica che FA_Id non sia già stato compilato, quindi già presente
- check_op/2			(OP, REX)	"operatore non corretto"	verifica che l'operatore sia corretto
- check_oneof/1			(REX)		"oneof non corretto"		verifica che oneof abbia solo simboli come espressioni regolari
- check_regexp/1		(REX)		"espr. reg. non corretta"	verifica che REX sia un'espressione regolare
- check_list/1			(Input)		"l'input non è una lista"	verifica che Input sia una lista
- nfa_error/1			(Err)						stampa a video il messaggio (Err) 

--------------------------------
AUTOMI PRINCIPALI
--------------------------------

a				|q0|  --- epsilon --->  |q1|  --- a --->  |q2|  --- epsilon --->  |q3|		

				



oneof(a, b, c)						|q1|  --- a --->  |q3|  
				|q0|  --- epsilon ---> 	|q1|  --- b --->  |q4|  --- epsilon --->  |q2|		
alt(a, b, c)						|q1|  --- c --->  |q5|  

			



seq(a, b, c)			|q0|  --- epsilon --->  |q1|  --- a --->  |q2|  --- b --->  |q3|  --- c --->  |q4|  --- epsilon --->  |q5|	

				



star(a)				|q0|  --- epsilon --->  |q1|  --- a --->  |q2|  --- a --->  |q2|  --- epsilon --->  |q3|
							|q1|  --- epsilon --->  |q3|	    |q2|  --- epsilon --->  |q1|




plus(a)				|q0|  --- epsilon --->  |q1|  --- a --->  |q2|  --- a --->  |q2|  --- epsilon --->  |q3|

	


							|q1|  --- a --->  |q2|  --- epsilon --->  |q3|
bar(a)				|q0|  --- epsilon --->  		  |q2|  --- A --->  |q4|  
							|q1|  --- A --->  |q4|  --- A --->  |q4|  --- epsilon --->  |q5|
							|q1|  --- epsilon --->  |q5|


Per quanto riguarda l'operatore bar, sono stati implementati anche i casi di:

					insieme originale			input riconosciuti

- bar(alt(a,b,c)) 			{a, b, c}				[], [epsilon], [a, a], [a, b], [a, b, c], etc.
- bar(oneof(a,b,c)) 			{a, b, c}				[], [epsilon], [a, a], [a, b], [a, b, c], etc.
- bar(seq(a,b,c)) 			{abc}					[], [epsilon], [a], [a, b], [a, b, c, d], etc.
- bar(star(a))			     	{epsilon, a, aa, aaa, ...}		[b], [b, b], [a, b], [a, a, b], etc. 
- bar(plus(a))				{a, aa, aaa, ...}			[], [epsilon], [b], [b, b], [a, b], [a, a, b], etc. 













