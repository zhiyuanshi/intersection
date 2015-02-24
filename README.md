# intersection

[Paper (PDF)](https://github.com/zhiyuanshi/intersection/blob/master/paper/main.pdf?raw=true)

## Dependencies

Make sure you have the following installed:

* [Ruby](https://www.ruby-lang.org/)
* [xelatex](http://www.xelatex.org/)
* [latexmk](http://www.ctan.org/pkg/latexmk/)

Install Microsoft TrueType core fonts:

    sudo apt-get update
    sudo apt-get install -y msttcorefonts

## Generating PDF

To make the PDF just once:

    rake

To watch for changes of source files and re-generate the PDF if necessary:

    rake watch
