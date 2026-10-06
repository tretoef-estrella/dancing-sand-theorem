# Web queries of cold reader 5 (one line each, time from `date`)
Mon Oct  5 19:09:57 CEST 2026 — curl -sIL https://doi.org/10.1080/00927872.2024.2347582 (does the DOI of [GMMY24] resolve?)
Mon Oct  5 19:09:57 CEST 2026 — curl -s 'https://oeis.org/A193134?fmt=text' (what is OEIS A193134?)
Mon Oct  5 19:10:04 CEST 2026 — curl -sL 'https://oeis.org/search?q=id:A193134&fmt=text' (retry; the first query returned nothing, exit 1)
