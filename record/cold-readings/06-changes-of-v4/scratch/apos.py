import re,sys
t=open(sys.argv[1],encoding='utf-8').read()
print('ASCII apostrophe', t.count("'"), 'U+2019', t.count('’'), 'U+2032', t.count('′'))
print(re.findall(r".{10}'.{5}", t))
