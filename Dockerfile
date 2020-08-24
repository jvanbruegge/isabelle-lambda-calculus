FROM makarius/isabelle:Isabelle2020

RUN for t in Nominal2 FinFun; do \
        curl https://www.isa-afp.org/release/afp-$t-current.tar.gz -o $t.tar.gz ; \
        cd Isabelle/src/ ; \
        tar -xzf ../../$t.tar.gz ; \
        cd .. ; \
        echo "src/$t" >> ROOTS ; \
        cd .. ; \
        rm $t.tar.gz ; \
    done

RUN ./Isabelle/bin/isabelle build -o system_heaps -b Nominal2

COPY ROOT Defs.thy Soundness.thy ./
