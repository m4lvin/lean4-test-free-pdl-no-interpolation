
build:
	lake build

doc: build
	lake build :literateHtml

show-doc: doc
	(sleep 2 && xdg-open http://127.0.0.1:8000/) &
	lake exe verso-serve .lake/build/literate-html
