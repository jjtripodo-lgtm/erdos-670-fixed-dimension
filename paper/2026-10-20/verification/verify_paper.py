"""Read-only checks for the 20 October public manuscript package."""
from pathlib import Path
import hashlib,json,zipfile,subprocess,sys
r=Path(__file__).resolve().parents[1]
def require(ok,msg):
    if not ok: raise ValueError(msg)
def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()
v=json.loads((r/"verification/PAPER_VALIDATION.json").read_text())
for key,path in [("source","Separated_Distances_in_Fixed_Dimension.tex"),("pdf","Separated_Distances_in_Fixed_Dimension.pdf"),("source_zip","Separated_Distances_in_Fixed_Dimension_source.zip")]:
    require(digest(r/path)==v[key+"_sha256"],key+" identity differs")
with zipfile.ZipFile(r/"Separated_Distances_in_Fixed_Dimension_source.zip") as z:
    require(sorted(z.namelist())==sorted(v["source_zip_files"]),"source ZIP inventory")
    for name in z.namelist(): require(z.read(name)==(r/name).read_bytes(),"ZIP byte mismatch: "+name)
source=(r/"Separated_Distances_in_Fixed_Dimension.tex").read_text()
parts=["preamble.tex","main_body.tex"]
assembled="\n".join((r/p).read_text() for p in parts)
assembled+="\n\\appendix\n"+"\n".join((r/p).read_text() for p in ["macro_appendix.tex","certificate_appendix.tex","source_correspondence.tex"])
assembled+="\n\\clearpage\n"+(r/"references.tex").read_text()+"\n\\end{document}\n"
require(assembled==source,"modular/assembled source differs")
require(source.count("The author thanks Boon Suan Ho for helpful comments on an earlier draft of this manuscript.")==1,"acknowledgment")
require("\\label[corollary]{cor:r29-all}" in source and "arxiv.org/abs/1002.0442v1" in source,"all-size corollary/source")
normal=subprocess.check_output([sys.executable,str(r/"certificate_reconstruction.py")])
optimized=subprocess.check_output([sys.executable,"-O",str(r/"certificate_reconstruction.py")])
require(normal==optimized,"optimization mismatch")
require(json.loads(normal)==json.loads((r/"verification/RECONSTRUCTION.json").read_text()),"certificate receipt differs")
require((r/"Separated_Distances_in_Fixed_Dimension.pdf").read_bytes().startswith(b"%PDF-"),"PDF header")
print("PASS: new paper/PDF/ZIP identity, source assembly, acknowledgment, exact rational certificate")
