# Match arXiv AutoTeX: pdfLaTeX only (not LuaLaTeX / XeLaTeX).
# scripts/build_arxiv_pdf.sh also passes -pdf -pdflatex=... explicitly.
$pdf_mode = 1;
$pdflatex = 'pdflatex -interaction=nonstopmode -halt-on-error %O %S';
