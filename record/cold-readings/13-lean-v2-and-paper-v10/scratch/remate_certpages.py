import subprocess
P='material/certificate/LEAN_CERTIFICATE_DANCING_SAND_v2.pdf'
keys=['Certificate v2','10.5281/zenodo.23298437','Version 2.','its equivalent form Syl','every 𝑛 ≥ 2 and Theorem 4.2','version 2 proves','Generality.','CheckCubo2','1.5 Version 2','SmallCases','V2READ','69 runs','a 69th','piece C53','C53','DepsCubo2','8 019','420','17 files','twenty-five','541','69 pieces','69 scripts','13:44','make_tables','MANIFEST_md5_420','version 10']
for p in range(1,28):
    t=subprocess.run(['pdftotext','-layout','-f',str(p),'-l',str(p),P,'-'],capture_output=True,text=True).stdout
    hits=[k for k in keys if k in t]
    print(p, hits)
