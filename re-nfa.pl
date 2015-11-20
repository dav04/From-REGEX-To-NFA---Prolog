%%%%    -*- Mode: Prolog -*-
%%%%    re-nfa.pl --

%%	Studente: Davide Medina
%%	Matricola: 780851

%%	Progetto Prolog:
%%	"Compilazione d'espressioni regolari in automi non deterministici"

%%%% ---------------------------------------------------------------------

%%	is_regexp(RE)
% Vero se risulta corretta l'espressione regolare (RE), che viene
% suddivisa in due liste, una con gli operatori principali e una con le
% loro espressioni regolari, in modo da controllare sia la correttezza
% degli operatori sia il corretto numero di espressioni regolari che
% possono avere, come bar, star e plus che possono averne solo una

is_regexp(RE) :-
	nonvar(RE),
	split_regexp(RE, OP, REX), !,
	catch(check_op(OP, REX), Err, nfa_error(Err)),
	catch(check_regexp(REX), Err, nfa_error(Err)).

%%	is_regexp_list(REX)
% Accetta una lista delle espressioni regolari (REX) contenute negli
% operatori
% Vero se l'argomento dell'operatore è un simbolo o un'espressione
% regolare

is_regexp_list([]).
is_regexp_list([REX | REXs]) :-
	atomic(REX), !,
	is_regexp_list(REXs).
is_regexp_list([REX | REXs]) :-
	is_regexp(REX), !,
	is_regexp_list(REXs).

%%	is_operator(OP, REX)
% Accetta una lista degli operatori (OP) e una lista delle espressioni
% regolari in essi contenuti (REX)
% Vero se l'operatore esiste e se oneof contiene solo simboli

is_operator([], _).
is_operator([OP | OPs], REX) :-
	is_operator(OP, REX),
	is_operator(OPs, REX).
is_operator(bar, _).
is_operator(star, _).
is_operator(plus, _).
is_operator(seq, _).
is_operator(alt, _).
is_operator(oneof, []).
is_operator(oneof, [REX | REXs]) :-
	catch(check_oneof(REX), Err, nfa_error(Err)),
	is_operator(oneof, REXs).

%%	split_regexp(RE, OP, REX)
% Accetta un'espressione regolare (RE) e restituisce una lista degli
% operatori (OP) e una lista delle rispettive espressioni regolari (REX)

% simbolo senza operatori
split_regexp(RE, [], [REX]) :-
	nonvar(RE),
	functor(RE, _, 0),
	RE =.. [REX].

% operatore con una singola espressione regolare
split_regexp(RE, [OP| OPs], REX) :-
	nonvar(RE),
	RE =.. [OP | [RE2]],
	split_regexp(RE2, OPs, REX).

% operatore con più espressioni regolari
split_regexp(RE, [OP], REX) :-
	nonvar(RE),
	RE =.. [OP | REX],
	OP \= star,
	OP \= plus,
	OP \= bar.

%%%% ---------------------------------------------------------------------

%%	nfa_compile_regexp(FA_Id, RE)
% Accetta un'identificatore (FA_Id) per l'automa, che sia una costante e
% che non esista già, e un'espressione regolare (RE), che
% viene verificata con is_regexp, suddivisa con split_regexp e, infine,
% considerata dall'interno verso l'esterno invertendo la lista degli
% operatori
% Vero se l'automa viene compilato correttamente

nfa_compile_regexp(FA_Id, RE) :-
	catch(check_id(FA_Id), Err, nfa_error(Err)),
	catch(check_id_exists(FA_Id), Err, nfa_error(Err)),
	is_regexp(RE),
	split_regexp(RE, OP, REX),
	reverse(OP, OP_r),
	assert(nfa_initial(FA_Id, q0)),
	gensym(q, N_State),
	assert(nfa_delta(FA_Id, q0, epsilon, N_State)),
	regexp_op_list(FA_Id, OP_r, REX, N_State, _Final, Final2),
	assert(nfa_final(FA_Id, Final2)),
	reset_gensym(q), !.

%%	regexp_op_list(FA_Id, OP, REX, Initial, Final, Final2)
% Crea un automa nel caso in cui abbiamo un'espressione regolare senza
% operatori; altrimenti indirizza ogni operatore al predicato regexp_op
% che creerà l'automa rispettivo.
% Sono distinti i casi in cui si ha un operatore preceduto da un bar
% (qui risulta dopo perchè la lista degli operatori è stata invertita)
% perchè solo tale operatore utilizza la variabile Final2

% espressione regolare senza operatori
regexp_op_list(FA_Id, [], [REX], Initial, Final, Final) :-
	var(Final),
	gensym(q, N_State),
	assert(nfa_delta(FA_Id, Initial, REX, N_State)),
	gensym(q, Final),
	assert(nfa_delta(FA_Id, N_State, epsilon, Final)).

regexp_op_list(_FA_Id, [], _REX, _Initial, Final, Final).

% operatore preceduto da bar
regexp_op_list(FA_Id, [OP, bar | OPs], REX, Initial, Final, Final3) :-
	regexp_op_bar(FA_Id, [OP, bar], REX, Initial, Final, Final2),
	regexp_op_list(FA_Id, OPs, REX, Initial, Final2, Final3).

% qualsiasi operatore
regexp_op_list(FA_Id, [OP | OPs], REX, Initial, Final, Final2) :-
	regexp_op(FA_Id, OP, REX, Initial, Final),
	regexp_op_list(FA_Id, OPs, REX, Initial, Final, Final2).

%%	regexp_op(FA_Id, OP, REX, Initial, Final)
% Crea l'automa secondo l'operatore (OP) ricevuto a partire dallo stato
% iniziale (Initial) e crea uno stato finale (Final)

%-----------------------------------------
%%	gestione dell'operatore oneof
% dato che risulta uguale all'operatore alt, con l'unica differenza che
% oneof gestisce solo simboli (controllato già da is_regexp), viene
% semplicemente richiamato il predicato che lo gestisce.

regexp_op(FA_Id, oneof, REX, Initial, Final) :-
	regexp_op(FA_Id, alt, REX, Initial, Final).

%-----------------------------------------
%%	gestione dell'operatore alt
% Viene creato uno stato finale comune a tutte le espressioni regolari
% contenute dall'alt e vengono gestiti i due casi in cui si hanno solo
% simboli oppure ulteriori operatori come espressioni regolari

regexp_op(_FA_Id, alt, [], _Initial, _Final).

% creazione stato finale comune
regexp_op(FA_Id, alt, REX, Initial, Final) :-
	var(Final),
	gensym(q, Final),
	regexp_op(FA_Id, alt, REX, Initial, Final).

% solo simboli come espressioni regolari
regexp_op(FA_Id, alt, [REX | REXs], Initial, Final) :-
	atomic(REX),
	gensym(q, N_State_2),
	assert(nfa_delta(FA_Id, Initial, REX, N_State_2)),
	assert(nfa_delta(FA_Id, N_State_2, epsilon, Final)),
	regexp_op(FA_Id, alt, REXs, Initial, Final).

% ulteriori operatori come espressioni regolari
regexp_op(FA_Id, alt, [REX | REXs], Initial, Final) :-
	split_regexp(REX, OP, REX2),
	reverse(OP, OP_r),
	regexp_op_list(FA_Id, OP_r, REX2, Initial, _Final2, Final3),
	assert(nfa_delta(FA_Id, Final3, epsilon, Final)),
	regexp_op(FA_Id, alt, REXs, Initial, Final).

%-----------------------------------------
%%	gestione dell'operatore seq
% Distinti i casi in cui si hanno solo simboli oppure ulteriori
% operatori come espressioni regolari ed inoltre, al raggiungimento
% dell'ultimo simbolo od operatore, viene creata una epsilon mossa che
% si collega direttamente allo stato finale

% ultimo simbolo della sequenza
regexp_op(FA_Id, seq, [REX], Initial, Final) :-
	atomic(REX),
	gensym(q, N_State),
	assert(nfa_delta(FA_Id, Initial, REX, N_State)),
	gensym(q, Final),
	assert(nfa_delta(FA_Id, N_State, epsilon, Final)).

% ultimo operatore della sequenza
regexp_op(FA_Id, seq, [REX], Initial, Final) :-
	split_regexp(REX, OP, REX2),
	reverse(OP, OP_r),
	regexp_op_list(FA_Id, OP_r, REX2, Initial, _Final2, Final3),
	gensym(q, Final),
	assert(nfa_delta(FA_Id, Final3, epsilon, Final)).

% gestione simboli sequenza
regexp_op(FA_Id, seq, [REX | REXs], Initial, Final) :-
	atomic(REX),
	gensym(q, N_State),
	assert(nfa_delta(FA_Id, Initial, REX, N_State)),
	regexp_op(FA_Id, seq, REXs, N_State, Final).

% gestione operatori sequenza
regexp_op(FA_Id, seq, [REX | REXs], Initial, Final) :-
	split_regexp(REX, OP, REX2),
	reverse(OP, OP_r),
	regexp_op_list(FA_Id, OP_r, REX2, Initial, _Final2, Final3),
	regexp_op(FA_Id, seq, REXs, Final3, Final).

%-----------------------------------------
%%	gestione dell'operatore star
% Viene creato l'automa in caso di un singolo simbolo come espressione
% regolare richiamando il plus ed aggiungendo un collegamento tra lo
% stato iniziale e lo stato finale in caso di stringa epsilon;
% altrimenti, viene collegato, con una epsilon mossa, lo stato iniziale
% allo stato finale di un automa precedentemente creato e vengono
% collegati allo stato iniziale tutti gli stati che a loro volta sono
% collegati con una epsilon mossa allo stato finale dell'automa già
% creato

% creazione automa con solo un simbolo come espressione regolare, quindi
% uguale al caso dell'operatore plus con l'aggiunta del collegamento
% epsilon tra stato iniziale e stato finale
regexp_op(FA_Id, star, [REX], Initial, Final) :-
	regexp_op(FA_Id, plus, [REX], Initial, Final),
	assert(nfa_delta(FA_Id, Initial, epsilon, Final)).

% dato un automa con già presente uno stato iniziale ed uno stato
% finale, vengono cercati gli stati collegati, tramite epsilon, allo
% stato finale e gestiti dal predicato find_delta_star collegandoli
% allo stato iniziale; inoltre viene creato un collegamento epsilon
% dallo stato iniziale allo stato finale
regexp_op(FA_Id, star, _REX, Initial, Final) :-
	findall(Q, nfa_delta(FA_Id, Q, epsilon, Final), State),
	find_delta_star(FA_Id, State, Initial),
	asserta(nfa_delta(FA_Id, Initial, epsilon, Final)).

%-----------------------------------------
%%	gestione dell'operatore plus
% Uguale all'operatore star senza l'aggiunta del collegamento epsilon
% dallo stato iniziale allo stato finale

% creazione automa con un solo simbolo come espressione regolare
regexp_op(FA_Id, plus, [REX], Initial, Final) :-
	atomic(REX),
	var(Final),
	gensym(q, N_State),
	assert(nfa_delta(FA_Id, Initial, REX, N_State)),
	assert(nfa_delta(FA_Id, N_State, REX, N_State)),
	gensym(q, Final),
	assert(nfa_delta(FA_Id, N_State, epsilon, Final)).

% dato un automa con già presente uno stato iniziale ed uno stato
% finale, vengono cercati gli stati collegati, tramite epsilon, allo
% stato finale e gestiti dal predicato find_delta_plus
regexp_op(FA_Id, plus, _REX, Initial, Final) :-
	findall(Q, nfa_delta(FA_Id, Q, epsilon, Final), State),
	find_delta_plus(FA_Id, State, Initial).

%-----------------------------------------
%%	gestione dell'operatore bar
% dato un simbolo come espressione regolare, si crea l'automa
% richiamando il caso in cui si ha un simbolo senza operatori e
% successivamente si creano degli stati che riconoscono un qualsiasi
% altro carattere tranne epsilon così da evitare il loop

regexp_op(FA_Id, bar, [REX], Initial, Final) :-
	var(Final),
	regexp_op_list(FA_Id, [], [REX], Initial, Pozzo, Pozzo),
	findall(Q, nfa_delta(FA_Id, Q, epsilon, Pozzo), [State]),
	gensym(q, N_State2),
	assert(nfa_delta(FA_Id, State, A, N_State2) :- A \= epsilon),
	assert((nfa_delta(FA_Id, Initial, A, N_State2) :- A \= epsilon)),
	assert((nfa_delta(FA_Id, N_State2, A, N_State2) :- A \= epsilon)),
	gensym(q, Final),
	assert(nfa_delta(FA_Id, N_State2, epsilon, Final)),
	assert(nfa_delta(FA_Id, Initial, epsilon, Final)).

%%	'regexp_op_bar(FA_Id, [OP, bar], REX, Initial, Final, Final2)
% Gestione degli operatori (OP) preceduti dall'operatore bar (qui
% risulta dopo perchè la lista degli operatori viene invertita)

%%	'bar(alt(...))
% Viene creato l'automa dell'operatore alt normale avendo così uno stato
% pozzo; si cercano gli stati ad esso collegati con epsilon e collegati
% a loro volta allo stato che riconosce qualsiasi altra stringa
% (N_State2) tramite il predicato find_delta_bar_alt

% creazione stato finale bar
regexp_op_bar(FA_Id, [alt, bar], REX, Initial, Final, Final) :-
	var(Final),
	gensym(q, Final),
	regexp_op_bar(FA_Id, [alt, bar], REX, Initial, Final, Final).

regexp_op_bar(FA_Id, [alt, bar], REX, Initial, Final, Final) :-
	gensym(q, Pozzo),
	regexp_op(FA_Id, alt, REX, Initial, Pozzo),
	findall(Q, nfa_delta(FA_Id, Q, epsilon, Pozzo), State),
	gensym(q, N_State),
	assert(nfa_delta(FA_Id, Initial, epsilon, N_State)),
	gensym(q, N_State2),
	find_delta_bar_alt(FA_Id, State, N_State2),
	assert(nfa_delta(FA_Id, N_State, _, N_State2)),
	assert(nfa_delta(FA_Id, N_State2, A, N_State2) :- A \= epsilon),
	assert(nfa_delta(FA_Id, N_State2, epsilon, Final)).

%%	'bar(oneof(...))
% Richiama il predicato che crea la bar(alt(...)) dato che è uguale
regexp_op_bar(FA_Id, [oneof, bar], REX, Initial, Final, Final) :-
	regexp_op_bar(FA_Id, [alt, bar], REX, Initial, Final, Final).

%%	'bar(seq(...))
% Viene creato l'automa dell'operatore seq e poi ogni stato, tranne lo
% stato pozzo, viene collegato allo stato che riconosce qualsiasi
% stringa (N_State) tramite il predicato find_delta_bar

% creazione stato final bar
regexp_op_bar(FA_Id, [seq, bar], REX, Initial, Final, Final) :-
	var(Final),
	gensym(q, Final),
	regexp_op_bar(FA_Id, [seq, bar], REX, Initial, Final, Final).
regexp_op_bar(FA_Id, [seq, bar], REX, Initial, Final, Final) :-
	regexp_op(FA_Id, seq, REX, Initial, Pozzo),
	gensym(q, N_State),
	find_delta_bar_seq(FA_Id, Initial, Pozzo, N_State),
	assert(nfa_delta(FA_Id, N_State, A, N_State) :- A \= epsilon),
	assert(nfa_delta(FA_Id, N_State, epsilon, Final)),
	assert(nfa_delta(FA_Id, Initial, epsilon, Final)).

%%	'bar(plus(...))
% Viene creato l'automa dell'operatore plus e lo stato collegato tramite
% epsilon (State) allo stato pozzo viene a sua volta collegato allo
% stato che riconosce qualsiasi altra stringa (N_State2)

regexp_op_bar(FA_Id, [plus, bar], [REX], Initial, Final, Final) :-
	var(Final),
	regexp_op(FA_Id, plus, [REX], Initial, Pozzo),
	findall(Q, nfa_delta(FA_Id, Q, epsilon, Pozzo), [State | _]),
	gensym(q, N_State),
	assert(nfa_delta(FA_Id, Initial, epsilon, N_State)),
	gensym(q, N_State2),
	assert(nfa_delta(FA_Id, State, A, N_State2) :- A \= epsilon),
	assert(nfa_delta(FA_Id, N_State, _, N_State2)),
	assert(nfa_delta(FA_Id, N_State2, A, N_State2) :- A \= epsilon),
	gensym(q, Final),
	assert(nfa_delta(FA_Id, N_State2, epsilon, Final)).

% caso in cui si crea il bar di plus con un automa già creato in
% precedenza, quindi con già presente uno stato finale (Final)
regexp_op_bar(FA_Id, [plus, bar], _REX, Initial, Final, Final2) :-
	gensym(q, N_State),
	assert(nfa_delta(FA_Id, Initial, epsilon, N_State)),
	gensym(q, N_State2),
	findall(Q, nfa_delta(FA_Id, Q, epsilon, Final), State),
	find_delta_plus(FA_Id, State, Initial),
	assert(nfa_delta(FA_Id, N_State, _, N_State2)),
	assert(nfa_delta(FA_Id, N_State2, A, N_State2) :- A \= epsilon),
	gensym(q, Final2),
	assert(nfa_delta(FA_Id, N_State2, epsilon, Final2)).

%%	'bar(star(...))
% Viene creato l'automa dell'operatore star e lo stato collegato tramite
% epsilon (State) allo stato pozzo viene collegato a sua volta
% allo stato che riconosce qualsiasi stringa (N_State2)

regexp_op_bar(FA_Id, [star, bar], [REX], Initial, Final, Final) :-
	var(Final),
	regexp_op(FA_Id, star, [REX], Initial, Pozzo),
	findall(Q, nfa_delta(FA_Id, Q, epsilon, Pozzo), [State | _]),
	gensym(q, N_State),
	assert(nfa_delta(FA_Id, Initial, epsilon, N_State)),
	gensym(q, N_State2),
	assert(nfa_delta(FA_Id, State, A, N_State2) :- A \= epsilon),
	assert(nfa_delta(FA_Id, N_State, A, N_State2) :- A \= epsilon),
	assert(nfa_delta(FA_Id, N_State2, A, N_State2) :- A \= epsilon),
	gensym(q, Final),
	assert(nfa_delta(FA_Id, N_State2, epsilon, Final)).

% caso in cui si crea il bar di star con un automa già creato in
% precedenza, quindi con già presente uno stato finale (Final)
regexp_op_bar(FA_Id, [star, bar], _REX, Initial, Final, Final2) :-
	gensym(q, N_State),
	assert(nfa_delta(FA_Id, Initial, epsilon, N_State)),
	gensym(q, N_State2),
	findall(Q, nfa_delta(FA_Id, Q, epsilon, Final), State),
	find_delta_star(FA_Id, State, Initial),
	assert(nfa_delta(FA_Id, N_State, A, N_State2) :- A \= epsilon),
	assert(nfa_delta(FA_Id, N_State2, A, N_State2) :- A \= epsilon),
	gensym(q, Final2),
	assert(nfa_delta(FA_Id, N_State2, epsilon, Final2)).

%%	'bar(bar(...))
% Viene annullata la doppia negazione avendo così l'espressione
% regolare originaria

regexp_op_bar(_FA_Id, [bar, bar], _REX, _Initial, _Final, _Final2).

%%	find_delta_star(FA_Id, Q, Initial)
% Data una lista (Q) degli stati collegati tramite epsilon allo stato
% finale, viene collegato ogni stato della lista allo stato iniziale
% (Initial)

find_delta_star(_FA_Id, [], _Initial).

% ricerca ulteriore degli stati collegati tramite epsilon allo stato Q
% della lista; in caso positivo, vengono aggiunti alla lista principale
find_delta_star(FA_Id, [Q | Qs], Initial) :-
	Q \= Initial,
	findall(QQ, nfa_delta(FA_Id, QQ, epsilon, Q), State),
	State \= [],
	append(State, Qs, New_Q),
	find_delta_star(FA_Id, New_Q, Initial).

% creazione dei collegamenti epsilon allo stato iniziale
find_delta_star(FA_Id, [Q | Qs], Initial) :-
	Q \= Initial,
	assert(nfa_delta(FA_Id, Q, epsilon, Initial)),
	find_delta_star(FA_Id, Qs, Initial).

% se Q risulta essere uguale allo stato iniziale, vengono considerati i
% restanti stati
find_delta_star(FA_Id, [_Q | Qs], Initial) :-
	find_delta_star(FA_Id, Qs, Initial).

%%	find_delta_plus(FA_Id, Q, Initial)
% Uguale al find_delta_star però senza l'ulteriore ricerca di epsilon
% mosse poichè con il plus non c'è il rischio di avere casi di loop

find_delta_plus(_FA_Id, [], _Initial).

find_delta_plus(FA_Id, [Q | Qs], Initial) :-
	Q \= Initial,
	assert(nfa_delta(FA_Id, Q, epsilon, Initial)),
	find_delta_plus(FA_Id, Qs, Initial).

find_delta_plus(FA_Id, [_Q | Qs], Initial) :-
	find_delta_plus(FA_Id, Qs, Initial).

%%	find_delta_bar_alt(FA_Id, Q, Final)
% Data una lista Q di stati, essi vengono collegati allo stato finale
% (Final) in modo che possano accettare qualsiasi altra stringa

find_delta_bar_alt(_FA_Id, [], _Final).

find_delta_bar_alt(FA_Id, [Q | Qs], Final) :-
	assert(nfa_delta(FA_Id, Q, A, Final) :- A \= epsilon),
	find_delta_bar_alt(FA_Id, Qs, Final).

find_delta_bar_alt(FA_Id, [_Q | Qs], Final) :-
	find_delta_bar_alt(FA_Id, Qs, Final).

%%	find_delta_bar(FA_Id, Initial, N_State, Final)
% Predicato utilizzato nel caso in cui si ha bar(seq(...)) e serve a
% collegare, a partire dallo stato finale della sequenza (N_State), ogni
% stato della sequenza allo stato finale (Final)

% caso base, cioè raggiungo lo stato iniziale della sequenza
find_delta_bar_seq(_FA_Id, Initial, N_State, _Final) :-
	N_State = Initial.

% cerco gli stati della sequenza e li collego allo stato finale
find_delta_bar_seq(FA_Id, Initial, N_State, Final) :-
	findall(Q, nfa_delta(FA_Id, Q, _, N_State), [State | _]),
	assert(nfa_delta(FA_Id, State, A, Final) :- A \= epsilon),
	find_delta_bar_seq(FA_Id, Initial, State, Final).


%%%% ---------------------------------------------------------------------

%%	nfa_recognize(FA_Id, Input)
% Vero se la lista di simboli (Input) viene riconosciuta dall'automa
% avente identificatore indicato (FA_Id)

nfa_recognize(FA_Id, Input) :-
	catch(check_id(FA_Id), Err, nfa_error(Err)),
	catch(check_list(Input), Err, nfa_error(Err)),
	%is_list(Input),
	nfa_initial(FA_Id, Initial),
	nfa_recognize_accept(FA_Id, Input, Initial), !.

%%	nfa_recognize_accept(FA_Id, Input, State)
% Predicato di supporto a nfa_recognize che "attraversa" l'automa a
% seconda della lista di simboli ricevuta (Input) e verifica che lo
% stato in cui si trova dopo aver computato l'ultimo simbolo corrisponda
% allo stato finale, accettando così il linguaggio riconosciuto
% dall'automa

% caso base che verifica se l'ultimo stato in cui ci si trova
% corrisponde allo stato finale
nfa_recognize_accept(FA_Id, [], Final) :-
	nfa_final(FA_Id, Final), !.

% ultimo simbolo della lista avente epsilon mossa prima e dopo la
% lettura del simbolo stesso così da poter accedere allo stato finale
nfa_recognize_accept(FA_Id, [Input], Initial) :-
	nonvar(Input),
	nfa_delta(FA_Id, Initial, epsilon, State),
	nfa_delta(FA_Id, State, Input, State1),
	nfa_delta(FA_Id, State1, epsilon, State2), !,
	nfa_recognize_accept(FA_Id, [], State2).

% ultimo simbolo della lista avente epsilon mossa solo dopo la lettura
% del simbolo per accedere allo stato finale
nfa_recognize_accept(FA_Id, [Input], Initial) :-
	nonvar(Input),
	nfa_delta(FA_Id, Initial, Input, State1),
	nfa_delta(FA_Id, State1, epsilon, State2), !,
	nfa_recognize_accept(FA_Id, [], State2).

nfa_recognize_accept(FA_Id, [Input | Inputs], Initial) :-
	nonvar(Input),
	nfa_delta(FA_Id, Initial, epsilon, State),
	nfa_delta(FA_Id, State, Input, State1), !,
	nfa_recognize_accept(FA_Id, Inputs, State1).

nfa_recognize_accept(FA_Id, [Input | Inputs], Initial) :-
	nonvar(Input),
	nfa_delta(FA_Id, Initial, Input, State1), !,
	nfa_recognize_accept(FA_Id, Inputs, State1).

% avanzamento di una epsilon mossa nel caso in cui non sia stato
% riscontrato nessun delta avente il simbolo indicato nella lista
nfa_recognize_accept(FA_Id, Input, Initial) :-
	nfa_delta(FA_Id, Initial, epsilon, State),
	nfa_recognize_accept(FA_Id, Input, State).

%%%% ---------------------------------------------------------------------
%%	nfa_clear
% Ripulisce la base di dati eliminando gli stati iniziali e finali
% e tutti i delta di qualsiasi automa creato in precedenza

nfa_clear :-
	retractall(nfa_delta(_, _, _, _)),
	retractall(nfa_initial(_, _)),
	retractall(nfa_final(_, _)).

%%	nfa_clear(FA_Id)
% Ripulisce la base di dati eliminando lo stato iniziale, finale e tutti
% i delta corrispondenti all'automa avente l'identificatore indicato
% (FA_Id)

nfa_clear_nfa(FA_Id) :-
	retractall(nfa_delta(FA_Id, _, _, _)),
	retractall(nfa_initial(FA_Id, _)),
	retractall(nfa_final(FA_Id, _)).

%%	nfa_list
% Elenca gli stati iniziali e finali e tutti i delta di qualsiasi automa
% creato in precedenza

nfa_list :-
	listing(nfa_delta(_, _, _, _)),
	listing(nfa_initial(_, _)),
	listing(nfa_final(_, _)).

%%	nfa_list(FA_Id)
% Elenca lo stato iniziale, finale e tutti i delta corrispondenti
% all'automa avente l'identificatore indicato (FA_Id)
nfa_list(FA_Id) :-
	listing(nfa_delta(FA_Id, _, _, _)),
	listing(nfa_initial(FA_Id, _)),
	listing(nfa_final(FA_Id, _)).

%%%% ---------------------------------------------------------------------
%%	Gestione delle eccezioni

%%	check_id(FA_Id)
% Richiamato dai predicati nfa_compile_regexp e nfa_recognize, verifica
% che l'identificatore dell'automa (FA_Id) non sia una variabile

check_id(FA_Id) :-
	not(atomic(FA_Id)),
	throw('L\'id dell\'automa non è corretto.'),
	fail.
check_id(FA_Id) :-
	atomic(FA_Id).

%%	check_id_exist(FA_Id)
% Richiamato dal predicato nfa_compile_regexp, verifica se esiste un
% altro automa con lo stesso identificatore (FA_Id) tramite l'eventuale
% presenza dello stato iniziale

check_id_exists(FA_Id) :-
	nfa_initial(FA_Id, _),
	throw('L\'id dell\'automa esiste già.'),
	fail.
check_id_exists(FA_Id) :-
	not(nfa_initial(FA_Id, _)).

%%	check_op(OP, REX)
% Richiamato dal predicato is_regexp, verifica che l'operatore (OP) sia
% corretto

check_op(OP, REX) :-
	not(is_operator(OP, REX)),
	throw('Operatore non corretto.'),
	fail.
check_op(OP, REX) :-
	is_operator(OP, REX).

%%	check_oneof(REX)
% Richiamato dal predicato is_operator, verifica che l'espressione
% regolare (REX) corrisponda ad un simbolo

check_oneof(REX) :-
	not(atomic(REX)),
	throw('Operatore oneof non corretto; può contenere solo simboli'),
	fail.
check_oneof(REX) :-
	atomic(REX).

%%	check_regexp(REX)
% Richiamato dal predicato is_regexp, verifica che l'espressione (REX)
% sia un'espressione regolare corretta

check_regexp(REX) :-
	not(is_regexp_list(REX)),
	throw('Espressione regolare non corretta.'),
	fail.
check_regexp(REX) :-
	is_regexp_list(REX).

%%	check_list(Input)
% Richiamato dal predicato nfa_recognize, verifica che l'input ricevuto
% (Input) sia una lista

check_list(Input) :-
	not(is_list(Input)),
	throw('L\'input inserito non è una lista.'),
	fail.
check_list(Input) :-
	is_list(Input).

%%	nfa_error(Err)
% Richamato dal predicato catch, stampa a video l'eventuale messaggio di
% errore (Err)

nfa_error(Err) :-
	print_message_lines(current_output,
			    ' ',
			    [begin(error, _), prefix('~NERROR: '), '~w' - [Err]]
			   ),
	fail.


:- dynamic nfa_initial/2.
:- dynamic nfa_final/2.
:- dynamic nfa_delta/4.

%%%%    End of file  -- re-nfa.pl --






