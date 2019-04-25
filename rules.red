Red []
#include %concat.red
find*: func [blk fn][forall blk [if fn blk/1 [return blk]] blk: head blk none]
upper-first: func [text][rejoin [uppercase first text next text]]
found: child: parent: none
persons: make hash! 100
clear-reactions 
foreach p persons [unset p]
clear persons
he: she: they: none
set-preload: does [
	system/lexer/pre-load: function [text part][
		punct: charset "?!." 
		parse text [some [x: 
			  remove punct ;(print ["punct:" mold x])
			| change [not #":" some #" " "is" some #" "] "  is " ;(print ["is:" mold x])
			| change [comma any #" " | some #" " "and" some #" "] "  and " ;(print ["and:" mold x])
			| skip
		]]
	] ()
]
unset-preload: does [system/lexer/pre-load: none]

;;;;;;;;;;;;;;;
; Main object
;;;;;;;;;;;;;;;
person!: [
	type: 'person 
	me: none
	sex: none
	name: none
	married to: none
	wife: is [either all [married to sex = 'male][married to]['unknown]]
	husband: is [either all [married to sex = 'female][married to]['unknown]]
	parents: [] 
	children: [] 

	;;;;;;;;;;;;;;;;;;;;;
	; Reactive relatives
	;;;;;;;;;;;;;;;;;;;;;
	father: is [
		either all [
			not empty? parents
			found: find* parents function [parent][
				male? parent
			]
		][found/1]['unknown]
	]
	mother: is [
		either all [
			not empty? parents
			found: find* parents function [parent][
				female? parent
			]
		][found/1]['unknown]
	]
	sons: is [
		either empty? found: collect [
			foreach child children [if male? child [keep child]]
		][none][found]
	]
	daughters: is [
		either empty? found: collect [
			foreach child children [if female? child [keep child]]
		][none][found]
	]

]

;;;;;;;;;;;;;;;;;;;;;;;;;;
; Nuclear query functions
;;;;;;;;;;;;;;;;;;;;;;;;;;

; Helpers
of: make op! func ['relation 'entity][to-path reduce [entity relation]]
excluding: make op! func ['relation 'entity][append relation entity]
 and: make op! func ['a 'b][
	either block? a [append a b][reduce [a b]]
]
engender: func [s a][
	compose/deep [
		has [x][
			collect [
				foreach x (a) [
					if (pick [male? female?] s) x [keep x]
				]
			]
		]
	]
]
male: func ['a][engender on a]
female: func ['a][engender off a]
relative: func [a b][
	compose/deep [
		(to-set-word a) has [x y][
			(either 3 = length? b ['exclude][]) collect [
				foreach x (either block? b/1 [to-paren compose [union (b/1)]][b/1]) [
					x: get x
					if y: (to-path reduce ['x b/2]) [
						keep y
					]
				]
			] (either 3 = length? b [compose/deep [reduce [(b/3)]]][])
		]
	]
]
are: make op! func [a b][
	append person! switch type?/word b [
		block! [head insert b to-set-word a]
		path! [relative a b]
	] ()
]

; Func descriptions
'siblings are (children of parents excluding me)
'brothers are (male siblings)
'sisters are (female siblings)
'uncles are (brothers of parents)
'aunts are (sisters of parents)
'nephews are (sons of siblings)
'nieces are (daughters of siblings)
'cousins are (children of (uncles  and aunts))
'grandparents are (parents of parents)
'grandfathers are (male grandparents)
'grandmothers are (female grandparents)
'great-grandparents are (parents of grandparents)
'great-grandfathers are (male great-grandparents)
'great-grandmothers are (female great-grandparents)
'grandchildren are (children of children)
'grandsons are (male grandchildren)
'granddaughters are (female grandchildren)
'great grandchildren are (children of grandchildren)
'great grandsons are (male great grandchildren)
'great granddaughters are (female great grandchildren)

unset 'are
unset 'male
unset 'female
unset ' and

;;;;;;;;;;;;;;;;;;
; Outer functions
;;;;;;;;;;;;;;;;;;

person: does [make deep-reactor! copy/deep person!]
male: func [p][p/sex: 'male p]
female: func [p][p/sex: 'female p]

 is: make op! function [a b][set a b ()]

'man  is male person
'woman  is female person

unset ' is

new person: function ['person][
	unless find persons person [append persons person]
	set person x: make deep-reactor! copy/deep person!
	x/name: form x/me: person
	set to-word append copy x/name pick ["'" "'s"] #"s" = last x/name 
		function ['relation] compose [either p: select (person) relation [p]['unknown]]
	x
]
is person: function ['p][
	either attempt [object? o: get p][o][new person :p]
]
 is: make op! function ['a 'b][ ;   #"^(200A)" or try #"^(2009)"?
	case [
		all [word? a block? b find words-of get a b/1][
			op: get to-word rejoin ["is " b/1 " of"] 
			foreach y b/2 [a op y]
		]
		all [word? a 'person = b][
			either attempt [object? o: get p][o][new person :p]
		]
		all [word? a find [boy man] b][
			set 'he a 
			put o: is person :a 'sex 'male 
			;if not o/age [o/age: switch b [boy ['young] man ['grown-up]]]
		]
		all [word? a find [girl woman] b][
			set 'she a 
			put o: is person :a 'sex 'female 
			;if not o/age [o/age: switch b [girl ['young] woman ['grown-up]]]
		]
		all [path? a any-word? b] [set a b]
	] ()
]
are: make op! function [a b][
	case [
		all [path? a block? b][
			op: to-word rejoin ["are " a/2 " of"]
			do reduce [b op a/1]
		]
		all [block? b block? b/2][
			foreach x b/2 [
				op: to-word rejoin ["are " b/1 " of"]
				do reduce [a op x]
			]
		]
		path? b [set b a]
		;x: get a is person :b append x b
	] ()
]
 and: make op! func ['a 'b][; 
	either block? a [
		is person :b
		append a b
	][
		is person :a
		is person :b
		reduce [a b]
	]
]

is parent of: make op! function ['a 'b][
	either find [he she] a [sex: a a: get a][set [he she] a]
	set 'they none
	x: is person :a
	either block? b [
		foreach y b [
			z: y
			y: is person :y
			unless find x/children z [append x/children z]
			unless find y/parents a [append y/parents a]
		]
	][
		y: is person :b
		unless find x/children b [append x/children b]
		unless find y/parents a [append y/parents a]
	]
	if find [he she] sex [
		x/sex: pick [male female] 'he = sex
	] ()
]
is child of: make op! function ['a 'b][
	either find [he she] a [sex: a a: get a][set [he she] a]
	set 'they none
	either block? b [
		:b are parents of :a
	][
		:b is parent of :a
	]
	if find [he she] sex [
		a: get a a/sex pick [male female] 'he = sex
	] ()
]
is father of: make op! function ['a 'b][ ; TBD Should check default parents and replace if needed
	either 'he = a [a: get a][set 'he a]
	set 'they none
	:a is parent of :b
	a: get a
	a/sex: 'male
	; Activate reactor
	foreach x a/children [x: get x x/parents: x/parents] ()
]
is mother of: make op! function ['a 'b][
	either 'she = a [a: get a][set 'she a]
	set 'they none
	:a is parent of :b
	a: get a
	a/sex: 'female
	foreach x a/children [x: get x x/parents: x/parents] ()
]
is son of: make op! function ['a 'b][
	either 'he = a [a: get a][set 'he a]
	set 'they none
	:a is child of :b
	a: get a
	a/sex: 'male
	; Activate reactor
	foreach x a/parents [x: get x x/children: x/children] ()
]
is daughter of: make op! function ['a 'b][
	either 'she = a [a: get a][set 'she a]
	set 'they none
	:a is child of :b
	a: get a
	a/sex: 'female
	foreach x a/parents [x: get x x/children: x/children] ()
]
is sibling of: make op! function ['a 'b][
	either find [he she] a [sex: a a: get a][set [he she] a]
	set 'they reduce [a b]
	s1: is person :a
	either block? b [
		foreach y b [; ? May be move down?
			probe y
			s2: is person :y
			; Uniting parents and their children (in ideal world)
			s1/parents: s2/parents: unique union s1/parents s2/parents
			foreach x s1/parents [
				probe x
				x: get x
				if not find x/children a [append x/children a]
				if not find x/children y [append x/children y]
			]
		]
	][
		s2: is person :b
		; Uniting parents and their children (in ideal world)
		s1/parents: s2/parents: unique union s1/parents s2/parents
		foreach x s1/parents [
			x: get x
			if not find x/children a [append x/children a]
			if not find x/children b [append x/children b]
		]
	]
	if find [he she] sex [x/sex: pick [male female] 'he = sex] ()
]
is sister of: make op! function ['a 'b][
	either 'she = a [a: get a][set 'she a]
	set 'they reduce [a b]
	:a is sibling of :b
	a: get a ;b: get b
	a/sex: 'female
	; Need to touch parent's children to activate reactor for daughters
	foreach p a/parents [p: get p p/children: p/children] ()
]
is brother of: make op! function ['a 'b][
	either 'he = a [a: get a][set 'he a]
	set 'they reduce [a b]
	:a is sibling of :b
	a: get a ;b: get b
	a/sex: 'male
	; Need to touch parent's children to activate reactor for sons
	foreach p a/parents [p: get p p/children: p/children] ()
]
is married to: make op! function ['a 'b][; Should set s/he, infer sex afterwards
	either find [he she] a [sex: a a: get a][set [he she] a]
	set 'they reduce [a b]
	x: is person :a
	y: is person :b
	x/married to: b
	y/married to: a
	if find [he she] sex [
		x/sex: pick [male female] 'he = sex
		y/sex: pick [female male] 'he = sex
	] ()
]
is husband of: make op! func ['a 'b][
	either 'he = a [a: get a][set 'he a]
	set 'they reduce [a b]
	:a is married to :b
	put get a 'sex 'male
	put get b 'sex 'female ()
]
is wife of: make op! func ['a 'b][
	either 'she = a [a: get a][set 'she a]
	set 'they reduce [a b]
	:a is married to :b
	put get a 'sex 'female
	put get b 'sex 'male ()
]

;;;;;;;;;;;;;;;;
; Func-factory
;;;;;;;;;;;;;;;;
 and: make op! func ['a 'b][; 
	either block? a [
		is person :b
		append a b
	][
		is person :a
		is person :b
		reduce [a b]
	]
]

make-plural-func: func [singular [word!] plural [word!]][
	plural: to-word rejoin ["are " plural " of"]
	singular: to-word rejoin ["is " singular " of"]
	set plural make op! function ['a 'b] compose/deep [
		either 'they = a [a: get a][set 'they a]
		set [he she] none
		foreach x a [:x (singular) :b] (quote ())
	]
]
make-plurals: func [singulars [block!] /local singular plural][
	foreach singular singulars [
		either block? singular [
			; Irreggular forms
			set [singular plural] singular
		][
			plural: to-word append form singular "s"
		]
		make-plural-func singular plural
	]
]
make-plurals [parent [child children] son daughter sibling brother sister]

;;;;;;;;;;;
; of-funcs
;;;;;;;;;;;
make-of-func: func [relation [word!]][
	set to-word rejoin [relation " of"] function [p] compose/deep [
		either block? p [append/only [(relation)] p][(to-path reduce['p relation])]
	]
]
make-of-funcs: func [relations [block!]][
	foreach relation relations [make-of-func relation]
]
make-of-funcs [
	father mother children parents sons daughters 
	siblings brothers sisters 
	uncles aunts nephews nieces cousins 
	grandparents grandfathers grandmothers 
	great-grandparents great-grandfathers great-grandmothers 
	grandsons great grandsons 
	granddaughters great granddaughters
]

;;;;;;;;;;;;;;;;
; Special funcs
;;;;;;;;;;;;;;;;

wife of: function [p][
	either all [p/married to p/sex = 'male] [p/married to]['unknown]
]
husband of: function [p][
	either all [p/married to p/sex = 'female] [p/married to]['unknown]
]

;;;;;;;;;;;;;;;;;;;
; Query functions
;;;;;;;;;;;;;;;;;;;

Who are: function ['person's 'relatives][
	upper-first rejoin [
		person's " " relatives " are " 
		either not empty? rel: do reduce [person's relatives][
			concat/last rel [[", "] " and "]
		]["not known"]
		dot
	]
]
Who is: func [p][
	switch type?/word p [
		path! [get p]
		word! [o: get p rejoin compose [o/me " is " (describe o)]]
		object! [rejoin compose [p/me " is " (describe p)]]
	]
]
describe: function [person][
	conn: ""
	collect [
		case/all [
			not empty? person/parents [
				keep switch/default person/sex [
					male ["son of "]
					female ["daughter of "]
				]["child of "]
				keep concat person/parents " and "
				conn: "; "
			]
			person/married to [
				keep conn
				keep switch/default person/sex [
					male ["husband of "]
					female ["wife of "]
				]["married to "]
				keep form person/married to
				conn: "; "
			]
			not empty? person/children [
				keep conn
				keep switch/default person/sex [
					male ["father of "]
					female ["mother of "]
				]["parent of "]
				keep concat/last person/children [[", "] " and "]
				conn: "; "
			]
			all [block? person/siblings not empty? person/siblings][
				keep conn
				keep switch/default person/sex [
					male ["brother of "]
					female ["sister of "]
				]["sibling of "]
				keep concat/last person/siblings [[", "] " and "]
			]
		] keep dot
	]
]
male?: func [p][p 'male = select get p 'sex]
female?: func [p]['female = select get p 'sex]
set-preload ()