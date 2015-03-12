# intersection

[Paper (PDF)](https://github.com/zhiyuanshi/intersection/blob/master/paper/main.pdf?raw=true)

## Dependencies

* [Ruby](https://www.ruby-lang.org/)
* [xelatex](http://www.xelatex.org/)
* [latexmk](http://www.ctan.org/pkg/latexmk/)
* Microsoft TrueType core fonts

All-in-one installation script for Ubuntu:

    sudo apt-get update
    sudo apt-get install -y texlive-xetex
    sudo apt-get install -y latexmk
    sudo apt-get install -y msttcorefonts

## Generating PDF

To make the PDF just once:

    rake

To watch for changes of source files and re-generate the PDF if necessary:

    rake watch
