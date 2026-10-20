"""Assemble the editable public paper without external files or services."""
from pathlib import Path
import subprocess, json
r=Path(__file__).resolve().parent
receipt=json.loads(subprocess.check_output(["python3",str(r/"certificate_reconstruction.py")],text=True))
(r/"verification/RECONSTRUCTION.json").write_text(json.dumps(receipt,indent=2)+"\n")
parts=["preamble.tex","main_body.tex"]
text="\n".join((r/p).read_text() for p in parts)
text+="\n\\appendix\n"+"\n".join((r/p).read_text() for p in ["macro_appendix.tex","certificate_appendix.tex","source_correspondence.tex"])
text+="\n\\clearpage\n"+(r/"references.tex").read_text()+"\n\\end{document}\n"
(r/"Separated_Distances_in_Fixed_Dimension.tex").write_text(text)
print("Assembled public manuscript; exact certificate PASS")
