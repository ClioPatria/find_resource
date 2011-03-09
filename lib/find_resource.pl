:- module(find_resource,
	  [ find_literal/3,   % +Text, +MatchType, -Literal
	    find_resource_by_name/3   % +Name, -Hits, +Options
	  ]).

:- use_module(library(semweb/rdf_db)).
:- use_module(library(semweb/rdfs)).
:- use_module(library(semweb/rdf_litindex)).

% force indexing
:- rdf_find_literals(zzz,_).


%%	find_resource_by_name(+Name:atom, +Attributes:list(P-D),
%%             -Hit:hit(Distance:nonneg,Hit:atom,Prop:atom,Label:atom),
%%             +Options)  is nondet.
%
%	Find a resource based on a Name.
%
%       Options
%       * Match
%	one of case, stem, prefix. Method to match the Name
%	against the literal index. Default is case
%
%	* Distance
%	Boolean, compute literal distance if true. Default is true. The
%	distance is based on two figures:
%		* Mismatch of the label
%		* Handicap of the attribute
%
%	* Attribute
%	List of the form Resource-Distance. Smaller
%	distance is better, so rdfs:label typically is 0.
%	If multiple attributes match, we take the best.

find_resource_by_name(Name, Hits, Options) :-
	rdf_equal(rdfs:label, P),
	option(match(Match), Options, case),
	option(distance(Distance), Options, true),
	option(attributes(Attributes), Options, [P-0]),
	catch(findall(D-Label, find_literal_distance(Distance, Name, Match, Label, D), Pairs),
	      no_stem(_),
	      fail),
 	findall(Hit, uri_with_label_in(Pairs, Attributes, Hit), Hits1),
	sort(Hits1, Hits2),			% sort by URI
	remove_dup_uris(Hits2, Hits3),	        % take lowest on URI
	sort(Hits3, Hits).			% sort by distance


remove_dup_uris([], []).
remove_dup_uris([hit(URI,D,P,L)|T0], [hit(D,URI,P,L)|T]) :-
	remove_same_uri(URI, T0, T1),
	remove_dup_uris(T1, T).

remove_same_uri(URI, [hit(URI,_,_,_)|T0], T) :- !,
	remove_same_uri(URI, T0, T).
remove_same_uri(_, L, L).

uri_with_label_in(LabelPairs, Attributes, hit(URI, Distance, P, Label)) :-
	member(D-Label, LabelPairs),
	rdf(URI, P, literal(Label)),
	\+ rdf(URI, rdf:type, 'http://semanticweb.cs.vu.nl/prestoprime/Tag'), % hack
	(   member(P-F, Attributes)
	->  true
	;   member(AS-F, Attributes),
	    rdfs_subproperty_of(P, AS)
	),
	Distance is D+F.


		 /*******************************
		 *	  find literals  	*
		 *******************************/

find_literal_distance(true, Tokens, MatchType, Label, Distance) :-
	!,
	find_literal(Tokens, MatchType, Label),
	literal_distance(Tokens, Label, Distance).
find_literal_distance(_, Tokens, MatchType, Label, 0) :-
	find_literal(Tokens, MatchType, Label).

%%	find_literal(+TextOrTokens, +MatchType, -Literal)
%
%	Find literal values that contain all Text where the
%       matching is determined by MatchType.
%	Text is either an atom or a list of tokens as produced by
%	rdf_tokenize_literal/2.
%	MatchType is one of case, stem or prefix.


find_literal(Text, MatchType, Literal) :-
	tokens(Text, Tokens),
	list_to_and(Tokens, MatchType, And),
	rdf_find_literals(And, Literals),
	member(Literal, Literals).


%%	list_to_and(+TextOrTokens, +MatchType, -AndTerm)
%
%	AndTerm is a conjunction of terms constructed from
%	MatchType and Token.
%
%	For performance reasons a conjunction of prefix items
%	is not made. Instead only the last conjunct gets a prefix.

list_to_and([], _, true).
list_to_and([One], MatchType, Match) :- !,
	mkmatch(MatchType, One, Match).
list_to_and([H|T], prefix, and(Match, And)) :- !,
        mkmatch(stem, H, Match),
        list_to_and(T, prefix, And).
list_to_and([H|T], MatchType, and(Match, And)) :-
	mkmatch(MatchType, H, Match),
	list_to_and(T, MatchType, And).


mkmatch(_, Number, Number) :-
	number(Number), !.
mkmatch(stem, Token, stem(Token)).
mkmatch(prefix, Token, prefix(Token)).
mkmatch(case, Token, case(Token)).

		 /*******************************
		 *	       DISTANCE		*
		 *******************************/

goal_expansion(forall(C0, A0), \+ (C, \+ A)) :-
	expand_goal(C0, C),
	expand_goal(A0, A).


%%	literal_distance(+Lit1, +Lit2, -Distance)
%
%	Compute the distance between two   literals. Distance values are
%	>= 0, where 0  means  perfect   match.  Handicaps  are  given to
%	inserted, deleted, moved and modified tokens.  See the above URL
%	for a description of the best edit-sequence comparing strings.

literal_distance(L1, L2, Distance) :-
	tokens(L1, TL1),
	tokens(L2, TL2),
	length(TL1, N1),
	length(TL2, N2),
	abs(N1-N2) =< min(N1, N2),	% too much difference in length
	cheapest_edit_path(TL1, TL2, EditCost, _Path),
	Distance is EditCost/max(N1,N2).

tokens(Tokens, Tokens) :-
	is_list(Tokens), !.
tokens(Spec, Tokens) :-
	atom(Spec), !,
	rdf_tokenize_literal(Spec, Tokens).
tokens(Number, [Number]) :-
	number(Number).


%%	cheapest_edit_path(+List1, +List2, -Distance, -Path)
%
%	Compute the cheapest edit path. As edit operations are weighted,
%	this is not necessarily the shorted   one,  but the algorithm is
%	basically the same.
%
%	@see http://www.ling.ohio-state.edu/~cbrew/2002/winter/684.02/string-distance.html

cheapest_edit_path(Toks1, Toks2, Distance, Path) :-
%	DelCost   = 10,			% Delete token
%	InsCost	  = 8,			% Insert token
	MatchCost = 0,			% Matched token
	CaseCost  = 1,			% Different case
	DWIMCost  = 3,			% Spelling error
	StemCost  = 5,			% Tokens have same stem
	SubstCost = 10,			% Replaced token
	MovCost   = 2,			% Token is moved

	T1 =.. [string|Toks1],
	T2 =.. [string|Toks2],
	functor(T1, _, M),
	functor(T2, _, N),
	X is M + 1,
	Y is N + 1,
	M1 is M - 1,
	N1 is N - 1,
	new_array(X, Y, Array),
	nb_set_array(Array, 0, 0, c(0, [])),
	forall(between(0, M1, I),
	       (   get_array(Array, I, 0, c(V0, P0)),
		   I1 is I+1,
		   arg(I1, T1, D),
		   del_cost(D, DC),
		   V is V0 + DC,
		   nb_link_array(Array, I1, 0, c(V, [del(D)|P0]))
	       )),
	forall(between(0, N1, J),
	       (   get_array(Array, 0, J, c(V0, P0)),
		   J1 is J+1,
		   arg(J1, T2, I),
		   ins_cost(I, IC),
		   V is V0 + IC,
		   nb_link_array(Array, 0, J1, c(V, [ins(I)|P0]))
	       )),
	forall(between(0, M1, I),
	       forall(between(0, N1, J),
		      (   I1 is I + 1,
			  J1 is J + 1,
		          arg(I1, T1, V1),
			  arg(J1, T2, V2),
			  (   V1 == V2
			  ->  Subst = MatchCost
			  ;   downcase_atom(V1, L),
			      downcase_atom(V2, L)
			  ->  Subst = CaseCost
			  ;   dwim_match(V1, V2)
			  ->  Subst = DWIMCost
			  ;   same_stem(V1, V2)
			  ->  Subst = StemCost
			  ;   Subst = SubstCost
			  ),
			  get_array(Array, I,  J, c(C1, P1)),
			  get_array(Array, I1, J, c(C2, P2)),
			  get_array(Array, I, J1, c(C3, P3)),

			  SubstC is C1 + Subst,
			  (   memberchk(del(V2), P2)
			  ->  del_cost(V2, DC2),
			      InsC is C2 - DC2 + MovCost
			  ;   ins_cost(V2, InsCost),
			      InsC is C2 + InsCost
			  ),
			  (   memberchk(ins(V1), P3)
			  ->  ins_cost(V1, IC1),
			      DelC is C3 - IC1 + MovCost
			  ;   del_cost(V1, DelCost),
			      DelC is C3 + DelCost
			  ),

			  (   SubstC < InsC
			  ->  (   SubstC < DelC
			      ->  nb_link_array(Array, I1, J1,
						c(SubstC, [subst(V1, V2)|P1]))
			      ;   nb_link_array(Array, I1, J1,
						c(DelC, [del(V1)|P3]))
			      )
			  ;   (   DelC < InsC
			      ->  nb_link_array(Array, I1, J1,
						c(DelC, [del(V1)|P3]))
			      ;   nb_link_array(Array, I1, J1,
						c(InsC, [ins(V2)|P2]))
			      )
			  )))),
%	pp_array(Array),
	get_array(Array, M, N, c(Distance, Path0)),
	reverse(Path0, Path).

ins_cost((,), 1) :- !.
ins_cost(_, 8).

del_cost((,), 1) :- !.
del_cost(_, 10).

same_stem(T1, T2) :-
	atom(T1), atom(T2), !,
	porter_stem(T1, Stem),
	porter_stem(T2, Stem).


		 /*******************************
		 *     SIMPLE ARRAY PACKAGE	*
		 *******************************/

new_array(X, Y, Array) :-
	Size is X * Y + 3,
	functor(Array, array, Size),
	arg(1, Array, 2),		% dimensions
	arg(2, Array, X),		% columns
	arg(3, Array, Y).		% rows

get_array(Array, X, Y, Val) :-
	arg(2, Array, Cols),
	Pos is X + Y*Cols + 4,
	arg(Pos, Array, Val).

nb_set_array(Array, X, Y, Val) :-
	arg(2, Array, Cols),
	Pos is X + Y*Cols + 4,
	nb_setarg(Pos, Array, Val).

nb_link_array(Array, X, Y, Val) :-
	arg(2, Array, Cols),
	Pos is X + Y*Cols + 4,
	nb_linkarg(Pos, Array, Val).
