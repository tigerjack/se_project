import os
directory = "../Alloy/Exported/Images"
extension = ".png"
files = [file for file in os.listdir(directory) if file.lower().endswith(extension)]

for file in files:
   print r"\begin{figure}[!htbp]"
   print r"\centering"
   print r"\includegraphics[width=\linewidth,keepaspectratio]{%s/%s}" % (directory, file)
   print r"\caption{File %s}" % file
   print r"\end{figure}"
   print r"\FloatBarrier"
