(* ================================================================ *)
(*  Selection Sort em Rocq                                          *)
(* ================================================================ *)

Require Import Arith List Lia.
Require Import Sorted.
Require Import Permutation.

Import ListNotations.

(** * Motivação

      O Selection Sort ordena uma lista repetindo o seguinte procedimento: escolhe o menor elemento 
    da parte ainda não ordenada da lista, coloca esse elemento na primeira posição dessa parte
     e repete o processo sobre o restante da lista.

    Só que notamos que para provar formalmente que o algoritmo está correto, não bastava mostrar
    que a saída está em ordem crescente. Também precisamos garantir que nenhum
    elemento foi perdido, duplicado ou criado.

    Pra isso, precisamos garantir que está ordenada e a saída está preservando os elementos da lista original

    - [Sorted le (ss l)]: Onde a lista (l) vai representar um resultado obtido pelo Selection Sort (ss) e [le] está ordenada usando a relação menor ou igual, e o resultado vai tá em ordem crescente.
    - [Permutation l (ss l)]: Tanto a lista original e a resultante possuem os mesmos elementos, a ordem pode ter mudado, mas nenhum valor será perdido, criado ou duplicado.
    *) 

(** * Um elemento é menor ou igual a todos os elementos da lista

      Estabelecemos quais propriedades precisariamos provar para a corretude do algorítmo, então pensamos em como representar a ideia do menor elemento.
    No Selection Sort, a cada etapa precisamos escolher um valor que seja menor ou igual à todos os outros elementos da parte da lista que ainda não foi ordenada. 
    Então criamos essa função, [le_all] (less than or equal to all), ou seja,
    menor ou igual a todos. Ela recebe dois argumentos: [x : nat], que [x] representa um número natural e [l]: [list nat], onde [l] representa uma lista de números naturais.
    O resultado da definição possui o tipo [Prop], então le_all(x, l) não produzirá uma nova lista, mas sim fará uma preposição lógica, que significa
    que uma afirmação que pode ter como valor: verdade, ou podemos identificar ela como falsa. A ideia da nossa definição é considerar qualquer elemento [y] que pertecer a uma lista [l].
    Todavia, precisaríamos provar que [x] é menor ou igual [y].
    Essa definição vai ser importante nas próximas etapas da prova, já que irá garantir que o elemento escolhido pela função da seleção é realmente o menor valor da lista.
  *)

Definition le_all (x : nat) (l : list nat) : Prop :=
  forall y, In y l -> x <= y.

(** * Seleção do menor elemento

      Agora que definimos le_all, o próximo passo seria pensar em como o selection sort faria para encontrar esse elemento quando for executado.
    Inicialmente, a primeira ideia seria utilizar uma função que receberia uma lista e devolveria o menor número, mas seria insuficiente e o pensamento estava errado.
    O selection sort não precisa saber somente qual é o menor valor, ele deveria continuar ordenando até o fim.
    Dessa forma pensamos que a função, na verdade, deveria devolver duas informações juntas: o menor elemento encontrado e a lista que foi formada pelos demais elementos    
    Então: 
    
    [select x l] considera os elementos da lista [x :: l].

    O resultado vai ser um par [(m, r)] o qual:

    - [m] é o menor elemento de [x :: l],
    - [r] seria todos os demais elementos,
    - [x :: l] então é uma permutação de [m :: r].
    
    Essa propriedade vai garantir que a função select não remova, duplique ou crie um elemento, só organizaria e separaria o menor elemento.

    Então a função na [select], definimos então como uma lógica recursiva, e para isso usamos [Fixpoint].
    Ela recebe dois argumentos: um números natural [x], que funcionaria como um candidato
    e uma lista [l], que terá os valores que ainda vamos analisar.
    
    O resultado possui o tipo [nat * list nat]. Isso é uma função que vai devolver um par formado pelo menor elemento e a lista com os restantes.
    E para a busca, a função vai analisar a estrutura da lista com [match l with].
    
    No caso base, seria [l = []], não tem mais elementos para comparar com o nosso candidato no momento. [X] será devolvido com o menor elemento e o restante da lista vazia.
    Já no segundo, a lista tem [h::t] (cabeça e cauda), e vamos comparar [h] com o candidato atual que é [x].
    Se for verdadeiro, [x] continua sendo nosso candidato, a função chama a si mesmo sobre a cauda, mantendo x e devolve um par [(m,r)], e como [h] não foi escolhido para continuar como candidato, ele precisa estar na lista restante, por isso o resultado (m,h::r).
    Caso seja falso, significa que [h] é menor [x]. Nessa caso, [h] passa a ser o novo candidato de menor elemento e chama a função de novo, e retorna a mesma estrutura de saída do caso verdade. Nesse caso o [x] não pode ser 
    descartado, então é anexado à lista do restantes.
    
    Dessa forma à cada etapa, o menor valor entre [x] e [h] continua sendo comparado com os próximos elementos, enquanto o outro valor é colocado na lista restante. O resultado da recursão [m] será o menor elemento e [r] possuirá o resto da lista.
    
    *)
    
Fixpoint select (x : nat) (l : list nat) : nat * list nat :=
  match l with
  | [] => (x, [])
  | h :: t =>
      if x <=? h then
        let '(m, r) := select x t in
        (m, h :: r)
      else
        let '(m, r) := select h t in
        (m, x :: r)
  end.

(** * Especificação da função [select]

    Este lema é o mais importante da primeira parte. Depois de definir [select], já podemos 
    executar a função, ela receberá um candidato [x], analisará [l] e devolverá um par [(m,r)].
    Observando que a função ao devolver o par não é o bastante para utilizarmos o [select], precisamos demonstrar
    formalmente que o resultado produzido por ela possui o comportamento que esperamos. Por isso criamos o lema [select_spec].
    Spec vem de specification, esse lema funcionará como um verificador da função: sempre que [select x l]
    devolve o par[(m,r)], algumas propriedades devem ser obrigatoriamente ser verdadeiras.
    
    A hipótese: 
    
    [[select x l = (m, r)]]
    
    Indica que ao executar [select] sobre os elementos de [x::1], o elemento
    que selecionamos como [x] e [l] são respectivamente [m] e a lista restante [r].
    A partir dessa hipótese, provaremos 3 propriedades, a primeira é: 
    
    [[ Permutation (x :: l) (m :: r)]]
    
    Ela vai garanti que a lista de entrada e a lista que foi produzida possui os mesmos elementos. A função altera posições.
    
    A segunda é:
    
    [[all m (x :: l)]]

    Vai garanti que [m] é menor ou igual à todos os elementos considerados pela função, então [m] representa o menor elemento de [x::1]
    
    A terceira é: 

    [[length r = length l]]

    Depois que o único elemeneto é separado como mínimo, a lista possui a forma [x :: 1]. O restante [r] deve possuir o mesmo tamanho [1]. Assim confirmamos que um elemento foi separado e nenhum outro elemento desapareceu durante o processo.
    Essas três propriedades juntas descrevem completamente o comportamento da função [select] e serão usadas mais adiante na prova do Selection Sort.

  *)

Lemma select_spec :
  forall x l m r,
    select x l = (m, r) ->
    Permutation (x :: l) (m :: r) /\
    le_all m (x :: l) /\
    length r = length l.
Proof.

    (** Começamos introduzindo [x] e [l]. Não colocamos [m], [r] e a hipótese sobre o resultado de [select], por que ainda precisamos decidir a estrutura que faremos a indução. *)

  intros x l.

  (** A função [select] é recursiva sobre a lista [l]. Então, nossa prova também será feita por indução.
      Durante a execução da função, o candidato ao menor elemento pode variar. Na chamada recursiva, podemos executar [select x t], mas em outra podemos executar [select h t].
      Se mantivéssemos [x] fixo no contexto antes da indução, a hipótese de indução poderia ficar específica demais e não poderia ser aplicada quando o candidato mudasse para [h].
      O comando [revert x] devolve [x] ao nosso objetivo. Garantindo com que a hipótese de indução será válida para qualquer candidato ao menor elemento. *)

  revert x.

    (** Nossa indução sobre [l] criará dois casos, sendo o primeiro em que [l = []] e o passo indutivo, em que [l = h :: t].
      Depois da divisão dos casos, colocaremos novamente o [x], o menor elemento [m], a lista restante [r] e a hipótese [Hselect]. *)

  induction l as [| h t IH]; intros x m r Hselect.

  - (* Caso base: l = [].
        Nesse momento, a função executada é:
       select x [] = (x, []). 
       Logo:
       - a lista [x] é permutação dela mesma;
       - x <= x;
       - os dois restos possuem tamanho zero. *)
    simpl in Hselect.
    inversion Hselect; subst m; subst r; clear Hselect.

        (** Nosso objetivo possui três propriedades conectadas por [/\\]. O primeiro [split] separa a propriedade de permutação das outras duas propriedades. *)

    split.

       (** Precisamos provar que [x :: []] é uma permutação de [x :: []]. Como as duas listas são iguais, usamos a reflexividade da relação de permutação. *)

    + apply Permutation_refl.

       (** Ainda restam duas propriedades conectadas por [/\\]:
          - [le_all x [x]];
          - [length [] = length []].
          Um novo [split] cria um objetivo para cada uma delas. *)

    + split.

        (** Para provar [le_all x [x]], abrimos a definição de [le_all]. *)

      * unfold le_all.

        (** Agora precisamos considerar um elemento qualquer [y] e uma hipótese [Hy] afirmando que [y] pertence à lista [x :: []]. *)

        intros y Hy.

        (** A simplificação transforma a hipótese de pertencimento em duas possibilidades, sendo elas: [y = x]; e [y] pertence à lista vazia. *)
        simpl in Hy.

        destruct Hy as [Hy | Hy].
        (** Na primeira possibilidade, sabemos que [y = x]. Substituímos [y] por [x] e precisamos provar [x <= x]. *)

        -- subst y.
           lia.
        (** A segunda possibilidade afirma que [y] pertence à lista vazia. Isso é impossível, portanto encerramos o caso por contradição. *)

        -- contradiction.

        (** Por fim, precisamos provar que o tamanho da lista restante vazia é igual ao tamanho da lista original vazia. Os dois lados são exatamente iguais. *)

      * reflexivity.

  - (** Passo indutivo: [l = h :: t].

        Nesse caso, [h] representa o primeiro elemento de [l] e [t] representa todos os elementos seguintes. Pela definição da função, o próximo comportamento depende do resultado da comparação entre [x] e [h]. *)
    simpl in Hselect.

    (** O comando [destruct] divide a nossa prova em duas partes:
        - Se x <= h for verdade ([true]);
        - Se x <= h for mentira ([false]).
        A gente guarda o resultado desse teste na hipótese [Hxh]. *)

    destruct (x <=? h) eqn:Hxh.

    + (* Caso x <= h.

         Como o nosso candidato x é menor ou igual a h, ele continua na disputa como o menor elemento e a gente roda a recursão na cauda t. 
         O elemento h que ficou de fora volta para a lista de elementos restantes. *)
      destruct (select x t) as [m' r'] eqn:Hrec.
      simpl in Hselect.

      (* A igualdade entre os pares deixa a gente substituir o m por m' e o r por h :: r'. 
      Feito isso, limpamos a hipótese Hselect que não serve mais. *)
      inversion Hselect; subst m; subst r; clear Hselect.

      (* Chamamos a hipótese de indução IH para o candidato x e a chamada recursiva Hrec.
         Ela joga no nosso contexto três coisas prontas:
         - Hperm: x :: t é permutação de m' :: r'
         - Hminimum: m' é menor ou igual a todo mundo em x :: t
         - Hlength: o resto r' tem o mesmo tamanho da cauda t *)
      specialize (IH x m' r' Hrec) as
          [Hperm [Hminimum Hlength]].

      (* Separamos a propriedade de permutação do resto das propriedades para resolver uma por uma. *)
      split.

      * (* Prova da permutação:
           Queremos mostrar que [x :: h :: t] é uma permutação de [m' :: h :: r'].
           A nossa IH é [x :: t] e [m' :: r'].
           Então, vamos fazer um mexer na lista em 3 passos usando transitividade:
           1. Troca x e h de lugar -> [h :: x :: t]
           2. Aplica a nossa Hperm na cauda -> [h :: m' :: r']
           3. Troca o h e o m' de lugar -> [m' :: h :: r'] *)
        eapply Permutation_trans.

        -- (* Passo 1: Trocamos os dois primeiros elementos (x e h) *)
           apply perm_swap.

        -- (* nos passos 2 e 3 usaremos a transitividade de novo para aplicar a IH e trocar depois *)
           eapply Permutation_trans.

           ++ (* Passo 2: Deixamos o h parado na frente e aplicamos a Hperm na cauda *)
              apply perm_skip.
              exact Hperm.

           ++ (* Passo 3: Trocamos os dois primeiros (h e m'). *)
              apply perm_swap.

      * (* Sobrou provar que o m' é o menor elemento e que os tamanhos batem. fazemos a separação de novo. *)
        split.

        -- (* Prova de que m' é menor ou igual a todo mundo de [x :: h :: t] *)
           unfold le_all in *.

           (* Consideramos um elemento qualquer y e a hipótese de que ele está na lista *)
           intros y Hy.
           simpl in Hy.

           (* Como o elemento y está na lista, ele só pode estar em 3 lugares:
              - Ou y = x
              - Ou y = h
              - Ou y está na cauda t.
              Analisamos cada caso *)
           destruct Hy as [Hy | Hy].

           ++ (* Primeiro caso: y = x.
                 Como a gente sabe que m' é menor ou igual a todo mundo de x :: t (pela IH), e o x está nessa lista, o m' com certeza é menor ou igual a x. *)
              subst y.
              apply Hminimum.
              simpl.
              left.
              reflexivity.

           ++ (* Se o y não for x, ele só pode ser h ou pertencer a t *)
              simpl in Hy.
              destruct Hy as [Hy | Hy].

              ** (* Segundo caso: y = h.
                    A IH nos diz que m' <= x. O teste do if deu que x <= h.
                    Ligando os pontos por transitividade, provamos que m' <= h. *)
                 subst y.
                 apply Nat.leb_le in Hxh.
                 eapply Nat.le_trans.

                 --- (* Mostramos que m' <= x usando a nossa hipótese de mínimo *)
                     apply Hminimum.
                     simpl.
                     left.
                     reflexivity.

                 --- (* E juntamos com a desigualdade do if (x <= h) *)
                     exact Hxh.

              ** (* Terceiro caso: y está na cauda t.
                    Essa está garantida direto pela nossa hipótese Hminimum. *)
                 apply Hminimum.
                 simpl.
                 right.
                 exact Hy.

        -- (* Prova do comprimento:
              Como o h voltou pro resto dos dois lados, os tamanhos continuam batendo.
              Só usamos a igualdade Hlength que a IH deu para nós. *)
           simpl.
           now rewrite Hlength.

    + (* Caso x <= h é falso.

         Isso significa que o h é menor que o x! Então o h assume como o novo candidato a mínimo e o x volta para a lista dos restantes. *)
      destruct (select h t) as [m' r'] eqn:Hrec.
      simpl in Hselect.

      (* Substituímos m por m' e r por x :: r' no contexto e limpamos o Hselect *)
      inversion Hselect; subst m; subst r; clear Hselect.

      (* Aplicamos a nossa hipótese de indução para a chamada de select h t *)
      specialize (IH h m' r' Hrec) as
          [Hperm [Hminimum Hlength]].

      split.

      * (* Prova da permutação:
           Queremos ir de [x :: h :: t] até [m' :: x :: r'].
           A ideia é fazer em 2 passos:
           1. Aplicamos a permutação da IH (h :: t ~ m' :: r') deixando o x na frente -> [x :: m' :: r']
           2. Trocamos o x e o m' de posição -> [m' :: x :: r'] *)
        eapply Permutation_trans.

        -- (* Passo 1: Deixamos o x na frente e usamos a Hperm na cauda *)
           apply perm_skip.
           exact Hperm.

        -- (* Passo 2: Trocamos as duas primeiras posições *)
           apply perm_swap.

      * (* Separamos a prova do mínimo e do comprimento restante *)
        split.

        -- (* Prova de que m' é menor ou igual a todo mundo de x :: h :: t *)
           unfold le_all in *.
           intros y Hy.
           simpl in Hy.

           (* Analisamos as 3 posições possíveis de y na lista: *)
           destruct Hy as [Hy | Hy].

           ++ (* Primeiro caso: y = x.
                 A IH nos dá que m' <= h. Como o if deu falso, sabemos que h < x (ou seja, h <= x).
                 Aí usamos transitividade para juntar as duas e fechar m' <= x. *)
              subst y.
              apply Nat.leb_gt in Hxh.
              eapply Nat.le_trans.

              ** (* Provamos m' <= h usando a hipótese Hminimum *)
                 apply Hminimum.
                 simpl.
                 left.
                 reflexivity.

              ** (* O lia resolve a matemática básica de h < x implicar em h <= x *)
                 lia.

           ++ (* Sobram os casos em que y = h ou y está na cauda t *)
              simpl in Hy.
              destruct Hy as [Hy | Hy].

              ** (* Segundo caso: y = h.
                    A hipótese Hminimum já garante direto que m' <= h. *)
                 subst y.
                 apply Hminimum.
                 simpl.
                 left.
                 reflexivity.

              ** (* Terceiro caso: y está na cauda t.
                    A nossa hipótese Hminimum também já reconhece isso de primeira. *)
                 apply Hminimum.
                 simpl.
                 right.
                 exact Hy.

        -- (* Prova do comprimento:
              Como o x voltou pro resto dos dois lados, basta usar a igualdade Hlength da IH *)
           simpl.
           now rewrite Hlength.

(** Assim fechamos o caso base e as duas ramificações do if.
    Provamos com sucesso que sempre que select devolve (m, r), as propriedades da especificação valem. *)
Qed.

(** * Consequências menores da especificação

    Depois que provamos o [select_spec], temos a descrição completa de como a função [select] funciona.

[[select x l = (m, r)]]

    Teremos três informações:
    - Que [x :: l] é uma permutação de [m :: r];
    - Que [m] é menor ou igual a todo mundo em [x :: l];
    - Que o tamanho do resto [r] é igual ao tamanho de [l].

    Só que nem sempre precisaremos usar essas três coisas ao mesmo tempo nas provas. Às vezes só queremos saber que os elementos foram mantidos com a permutação, outras vezes só precisamos do mínimo, ou só do tamanho.
    Para não ter que ficar abrindo o [select_spec] e limpando o que não importa toda hora, criamos três lemas menores. Cada um deles puxa só uma parte do que o [select_spec] garante. *)

(** ** Preservação dos elementos

    O lema [select_perm] serve para isolar a primeira parte do [select_spec].
    O objetivo dele é provar que, se o [select] pegou uma lista [x :: l] e devolveu [(m, r)], os elementos continuam sendo exatamente os mesmos no final. A ordem até pode mudar, mas ninguém some, duplica ou é criado do nada.*)

Lemma select_perm :
  forall x l m r,
    select x l = (m, r) ->
    Permutation (x :: l) (m :: r).
Proof.
  (* Introduzimos as variáveis e a nossa hipótese H do select *)
  intros x l m r H.
  
  (* Aqui a gente chama o select_spec. Como ele garante as três propriedades, usamos o padrão [Hperm _] para guardar só a permutação na hipótese Hperm, e o "_" diz para o Coq ignorar o resto das informações que não vamos usar agora *)
  destruct (select_spec x l m r H) as [Hperm _].
  
  (* O objetivo é exatamente o que guardamos em Hperm, então fechamos com exact *)
  exact Hperm.
Qed.


(** ** O elemento selecionado é realmente o menor de todos

    O lema [select_minimum] faz a mesma coisa, mas isola a segunda propriedade ele garante que o [m] que o [select] devolve é de fato menor ou igual a qualquer elemento da lista original.*)

Lemma select_minimum :
  forall x l m r,
    select x l = (m, r) ->
    le_all m (x :: l).
Proof.
  intros x l m r H.
  
  (* Dessa vez, pulamos a primeira propriedade (com o _), guardamos a segunda em Hminimum e ignoramos a terceira *)
  destruct (select_spec x l m r H) as [_ [Hminimum _]].
  
  exact Hminimum.
 Qed.


(** ** Tamanho da lista restante

    O lema [select_length] isola a última parte e nos mostra que depois de tirar o menor elemento, a lista que sobra ([r]) tem o mesmo tamanho da cauda original ([l]). Isso prova que a gente tirou exatamente um elemento e não perdeu nada no caminho.*)

Lemma select_length :
  forall x l m r,
    select x l = (m, r) ->
    length r = length l.
Proof.
  intros x l m r H.
  
  (* Ignoramos as duas primeiras propriedades e guardamos só a igualdade de tamanhos em Hlength *)
  destruct (select_spec x l m r H) as [_ [_ Hlength]].
  
  exact Hlength.
Qed.


(** * O mínimo também é menor ou igual aos elementos restantes

    A nosso lemma dirá que o [m] é menor ou igual a todo mundo da lista original [x :: l].
    Só que no Selection Sort, depois que colocamos esse [m] na primeira posição, o algoritmo vai continuar ordenando só a lista que restou ([r]).
    
    Por isso, precisamos de uma prova que garanta que o [m] também é menor ou igual a todos da lista restante [r] ([le_all m r]).
    Para provar isso, vamos usar duas coisas que já temos:
    - [x :: l] é uma permutação de [m :: r];
    - [m] é menor ou igual a todo mundo em [x :: l].
    Como uma permutação não muda quais elementos estão na lista (só a ordem), qualquer elemento de [r] também está na lista original. Então, se [m] era menor que todos os elementos, ele continua sendo menor que todo mundo em [r].*)

Lemma select_le_all_rest :
  forall x l m r,
    select x l = (m, r) ->
    le_all m r.
Proof.
  intros x l m r Hselect.
  
  (* Aqui pegamos as provas de permutação e de mínimo que fizemos nos lemas anteriores *)
  pose proof (select_perm x l m r Hselect) as Hperm.
  pose proof (select_minimum x l m r Hselect) as Hminimum.

  (* Abrimos a definição de le_all para podermos trabalhar com os elementos de fato *)
  unfold le_all in *.
  intros y Hy.

  (* Para provar que m <= y, a gente aplica o Hminimum. 
     Isso muda o nosso objetivo, agora só precisamos mostrar que esse y também fazia parte da lista original [x :: l] *)
  apply Hminimum.

  (* Como sabemos que x :: l é permutação de m :: r, usamos o Permutation_in para levar a informação de pertencimento de volta. Viramos a permutação do avesso para bater os lados *)

  eapply Permutation_in.
  - apply Permutation_sym.
    exact Hperm.
  - (* Agora provamos que y está em m :: r. Como a hipótese Hy diz que y está em r, basta dizer que ele está do lado direito, ou seja, na cauda da lista m :: r *)
    simpl.
    right.
    exact Hy.
Qed.


(** * Interface semelhante à função original [select_min]

    A nossa nova função [select] devolve um par [(m, r)] para o Selection Sort continuar.
    Só que, para manter as coisas parecidas com o projeto original, que tinha uma função [select_min] que só devolvia o menor elemento, criamos essa função aqui de interface.
    
    Ela utiliza o [select] por dentro.
    Como a lista pode vir vazia, usamos o tipo [option nat]:
    - Ela devolve [None] se a lista estiver vazia.
    - E [Some m] com o menor valor se tiver elementos.*)

Definition select_min (l : list nat) : option nat :=
  match l with
  | [] => None
  | x :: xs => Some (fst (select x xs))
  end.


(** Aqui a gente prova que a nossa interface está certa, se ela devolver [Some m], então esse [m] realmente é menor ou igual a todo mundo na lista [l]. *)

Lemma select_min_correct :
  forall l m,
    select_min l = Some m ->
    le_all m l.
Proof.
  intros l m H.
  destruct l as [| x xs].

  - (* Caso l = []: O select_min daria None, mas a hipótese diz que deu Some m. 
       Como None e Some são coisas totalmente diferentes, o Coq vê que isso é impossível e descarta com o discriminate *)
    simpl in H.
    discriminate.

  - (* Caso l = x :: xs (lista não vazia): 
       Abrimos o select x xs para ver o par [m' r] e usamos o lema select_minimum que já provamos *)
    simpl in H.
    destruct (select x xs) as [m' r] eqn:Hselect.
    simpl in H.
    pose proof (select_minimum x xs m' r Hselect) as Hminimum.
    
    (* O inversion mostra que m' e m precisam ser iguais. Aí a gente limpa e o Hminimum vira exatamente o nosso objetivo *)
    inversion H; subst; clear H.
    exact Hminimum.
Qed.


(** * Função principal do Selection Sort

    O Coq/Rocq é meio dificil com funções recursivas, ele exige que a gente garanta que a função vai terminar e não vai ficar rodando para sempre.
    Como a nossa função [select] diminui a lista de um jeito que não é tão óbvio visualmente, a gente usa um parâmetro "combustível" ([fuel]).
    
    Toda vez que a função faz uma chamada recursiva, ela gasta 1 unidade de combustível. Se o combustível chegar a 0, ela para.
    Na nossa função principal [ss], passamos o próprio tamanho da lista como combustível inicial. Como a cada passo do Selection Sort ordenamos um elemento, esse combustível é perfeito e suficiente para terminar o trabalho.*)

Fixpoint ss_fuel (fuel : nat) (l : list nat) : list nat :=
  match fuel with
  | 0 => []
  | S fuel' =>
      match l with
      | [] => []
      | x :: xs =>
          (* Selecionamos o menor m e o resto r *)
          let '(m, r) := select x xs in
          (* Colocamos m na frente e ordenamos o resto r com menos combustível *)
          m :: ss_fuel fuel' r
      end
  end.

(* Esta é a função que o usuário final vai usar de verdade, ela só pede a lista e calcula o combustível sozinha *)
Definition ss (l : list nat) : list nat :=
  ss_fuel (length l) l.


(** * Lemas auxiliares para a prova da ordenação *)

(** Aqui provamos que, se sabemos que "x é menor ou igual a todo mundo em l1", e l1 é uma permutação de l2, então "x também é menor ou igual a todo mundo em l2".*)

Lemma le_all_perm :
  forall x l1 l2,
    Permutation l1 l2 ->
    le_all x l1 ->
    le_all x l2.
Proof.
  intros x l1 l2 Hperm Hall.
  unfold le_all in *.
  intros y Hy.

  (* Queremos mostrar x <= y. Usamos o Hall, que precisa provar que y está em l1 *)
  apply Hall.

  (* Usamos a permutação simétrica para provar que, como y está em l2, ele também está em l1 *)
  eapply Permutation_in.
  - apply Permutation_sym.
    exact Hperm.
  - exact Hy.
Qed.


(** Ultiziamos o predicado [Sorted] para dizer que uma lista está ordenada. 
    Para provar que [x :: l] está ordenada, precisamos mostrar que o [x] é menor ou igual à cabeça de [l]. 
    A biblioteca chama isso de [HdRel le x l]. 
    Esse lemma prova que, se o x é menor que todo mundo ([le_all x l]), ele com certeza é menor que a cabeça. *)

Lemma le_all_HdRel :
  forall x l,
    le_all x l ->
    HdRel le x l.
Proof.
  intros x l Hall.
  destruct l as [| y ys].

  - (* Se a lista é vazia, não tem cabeça para comparar, então o caso é trivial *)
    constructor.

  - (* Se a lista é y :: ys, precisamos mostrar que x <= y *)
    constructor.
    apply Hall.
    simpl.
    left.
    reflexivity.
Qed.


(** * Correção da função com combustível

    Esta é segunda parte do trabalho é muito importante.
    O lemma [ss_fuel_correct] vai provar duas coisas juntas de uma vez só:
    - Que a lista de saída está ordenada ([Sorted]);
    - Que a lista de saída é uma permutação da original.
    
   Fazemos essa prova usando indução no número [n], que representa o combustível e, por tabela, o tamanho da lista, a hipótese [length l = n]. *)

Lemma ss_fuel_correct :
  forall n l,
    length l = n ->
    Sorted le (ss_fuel n l) /\
    Permutation l (ss_fuel n l).
Proof.
  induction n as [| n IH]; intros l Hlength.

  - (* Caso Base: n = 0.
       Se o tamanho da lista é 0, ela tem que ser vazia. *)
    destruct l as [| x xs].

    + (* Se for vazia, o ss_fuel devolve vazio. 
         A lista vazia está ordenada e é permutação de si mesma. *)
      simpl.
      split.
      * constructor.
      * constructor.

    + (* Se não for vazia, daria um tamanho maior que 0, o que quebra a hipótese. Contradição descartada. *)
      simpl in Hlength.
      discriminate.

  - (* Passo Indutivo: n = S n.
       O combustível é maior que 0, então a lista não pode ser vazia. *)
    destruct l as [| x xs].

    + (* Se a lista fosse vazia daria erro de tamanho de novo *)
      simpl in Hlength.
      discriminate.

    + (* Caso em que a lista é x :: xs. 
         Sabemos que o tamanho dela é S n, o que significa que o tamanho da cauda xs é exatamente n. *)
      simpl in Hlength.
      assert (Hxs_length : length xs = n) by lia.

      (* Rodamos um passo do algoritmo, o select na cabeça e na cauda *)
      simpl.
      destruct (select x xs) as [m r] eqn:Hselect.

      (* Pelo lema select_length, o resto r tem o mesmo tamanho de xs, ou seja, tamanho n *)
      pose proof (select_length x xs m r Hselect) as Hr_length.
      assert (Hr_length_n : length r = n) by lia.

      (* Agora que o tamanho de r é n, a gente pode usar a nossa hipótese de indução (IH).
         Isso nos dá duas coisas prontas, a ordenação recursiva de r que está ordenada e é permutação de r. *)
      specialize (IH r Hr_length_n) as
          [Hsorted_rec Hperm_rec].

      (* Pegamos também as propriedades da etapa do select que rodamos agora *)
      pose proof (select_perm x xs m r Hselect) as Hperm_select.
      pose proof (select_le_all_rest x xs m r Hselect) as Hminimum_r.

      (* Como a chamada recursiva só embaralha os elementos de r, se o m era menor que todo mundo de r, ele continua sendo menor que todo mundo na lista que foi ordenada recursivamente *)
      assert (Hminimum_output : le_all m (ss_fuel n r)).
      {
        eapply le_all_perm.
        - exact Hperm_rec.
        - exact Hminimum_r.
      }

      (* Agora provamos o split do nosso objetivo final (Ordenado e Permutação) *)
      split.

      * (* Prova de que está Ordenado:
           - A cauda já está ordenada por indução e o elemento m é menor que a cabeça da cauda, provado usando o le_all_HdRel *)
        constructor.
        -- exact Hsorted_rec.
        -- apply le_all_HdRel.
           exact Hminimum_output.

      * (* Prova de que é Permutação:
           A gente sabe que a lista original vira m :: r.
           E sabemos por indução que r vira a lista ordenada. 
           Juntando as duas coisas por transitividade, provamos a permutação final *)
        eapply Permutation_trans.
        -- exact Hperm_select.
        -- apply perm_skip.
           exact Hperm_rec.
Qed.


(** * Teorema final

    A nossa função [ss l] chama o [ss_fuel] passando exatamente o [length l]. 
    Como isso bate direitinho com o que o lemma [ss_fuel_correct] pede. A prova fecha por reflexividade.*)

Theorem selectionsort_correct :
  forall l,
    Sorted le (ss l) /\
    Permutation l (ss l).
Proof.
  intro l.
  unfold ss.
  apply ss_fuel_correct.
  reflexivity.
Qed.


(** * Exemplos executáveis

    Exemplos para testar. *)

Compute ss [3; 1; 4; 1; 2].
Compute ss [5; 4; 3; 2; 1].
Compute ss [].

Example selection_sort_example :
  ss [3; 1; 4; 1; 2] = [1; 1; 2; 3; 4].
Proof.
  reflexivity.
Qed.


(** Repositório-base: https://github.com/flaviodemoura/selection_sort *)
