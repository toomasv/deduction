Red [Title: "Explore inference"]
;https://toomasv.red/images/Deduction/infer.gif
context [
#include %rules.red

punct: charset "?!." 
prepare: func [text][
	parse text [some [x: 
		  remove punct ;(print ["punct:" mold x])
		| change [not #":" some #" " "is" some #" "] "  is " ;(print ["is:" mold x])
		| change [comma any #" " | some #" " "and" some #" "] "  and " ;(print ["and:" mold x])
		| skip
	]]
	text
]

view [
	title "Toy inference engine on genealogy"
	style ar: area 500x300 wrap on-key-down [
		if event/ctrl? [
			switch event/picked [
				32 [
					append face/text #"^(2002)" 
					face/selected: as-pair l: 1 + length? face/text l - 1
				]
				;73 [
				;	append face/text rejoin [#"^(200A)" "is"] ;  is
				;	face/selected: as-pair l: 1 + length? face/text l - 1
				;]
			]
		]
	]
	tab-panel [
		"Facts" [
			below
			facts: ar focus with [text: read %facts.red]
			return
			button "Enter" [
				do prepare copy facts/text
			]
			button "Clear" [clear-reactions foreach p persons [unset p]]
			button "Reload" [facts/text: read %facts.red]
			button "Save" [write %facts.red facts/text]
		]
		"Query" [
			query: ar 500x140 {Who is Jay?}
			button "Answer" [
				append clear response/text do prepare copy query/text
			]
			return
			response: ar 500x140 ""
		]
		"Rules" [
			below
			rules: ar {}
			return
			button "Enter" [
				do rules/text
			]
			button "Load" [
				rules/text: read %rules.red
			]
		]
	]
]
]