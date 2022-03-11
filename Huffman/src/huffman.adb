--------------------------------------------------------------------------------
-- ÁRBOL DE HUFFMAN
-- AUTOR: SERGI MORENO PÉREZ
--------------------------------------------------------------------------------
-- IMPORTACIÓN PAQUETES NECESARIOS
with Ada.Text_IO; use Ada.Text_IO;
with d_conjunto; with darbolbinario; with d_priority_queue;

procedure Huffman is
   -- DECLARACIONES
   -- declaración subtipo de char que será el tipo key del conjunto
   subtype alfabet is Character range ' ' .. 'z';
   -- uso del package d_conjunto almacenar los valores clave-valor de fichero
   package d_taula_frequencies is new d_conjunto(key => alfabet,item => Integer);
   use d_taula_frequencies;

   -- declaración record node formado por un char y un integer (frecuencia
   -- aparición en fichero)
    type node is record
      caracter : Character;
      frequencia : integer;
   end record;
   -- uso del package darbol binario con nodos del tipo record node
   package darbre is new darbolbinario ( elem => node );
   use darbre;

   -- Tipo puntero al tipo arbol
   type parbol is access arbol;
   -- implementación de la función menor y major del package d_priority_queue
   -- de items parbol

   function menor(a1 , a2 : in parbol) return boolean is
      x1, x2: node;
      menor : Boolean := False;
   begin
      raiz(a1.all,x1);
      raiz(a2.all,x2);
      return x1.frequencia < x2.frequencia;
   end menor;

   function major(a1 , a2 : in parbol) return boolean is
      x1, x2: node;
   begin
      raiz(a1.all,x1);
      raiz(a2.all,x2);
      return x1.frequencia > x2.frequencia;
   end major;
   -- uso del packeage d_priority_queue para almacenar los parbol
   package d_priority_queue_arbol is new d_priority_queue (size => 20 ,item => parbol ,"<" => menor ,">" => major );
   use d_priority_queue_arbol;

   -- definición record tcodi formado por una array de subtipos codigo y un natural
   -- que representará la longitud del array
   subtype codigo is Character range '0'..'1';
   type array_codigo is array(1..25) of codigo;
   type tcodi is record
      c : array_codigo;
      l : Natural;
   end record;


   -- definición variable global tipo conjunto para almacenar las claves tipo alfabet
   -- junto con su valor entero correspondiente que encontramos en el fichero "entrada.txt"
   c : conjunto;
   -- cola de prioridad donde almacenaremos punteros a árbol cuya raíz son tipos nodo
   colaP : priority_queue;
   -- puntero al árbol de Huffman que habremos generado
   paUnion : parbol;

   -- PROCEDURES Y FUNCTIONS

   -- PROCEDIMIENTO tratarLinea LLEVA A CABO EL TRATAMIENTO DE UNA LÍNEA DE
   -- FICHERO AÑADIENDO NUEVOS CARÁCTERES ENCONTRADOS AL MAPPING O AUMENTANDO
   -- SU VALOR
   procedure tratarLinea(c : in out conjunto; l : in String; leng : in Integer) is
      it : iterador;
      alfa,alfa_aux : alfabet;
      int : Integer;
      encontrado : Boolean := False;
   begin
      for i in 1..leng loop
         alfa := l(i);
         primero(c,it);
         while (es_valido(it) AND encontrado = False) loop
            obtener(c,it,alfa_aux,int);
            if (alfa_aux = alfa) then
               encontrado := True;
            else
               siguiente(c,it);
            end if;
         end loop;

         if encontrado = True then
            actualiza(c,alfa,int+1);
            encontrado := False;
         else
            poner(c,alfa,1);
         end if;
      end loop;
   end tratarLinea;

   -- PROCEDIMIENTO mappingFichero GENERA EL MAPPING DE LOS CARÁCTERES ALFABÉTICOS
   -- EXTRAÍDOS DEL FICHERO CUYO NOMBRE SERÁ PASADO POR PARÁMETRO
   procedure mappingFichero(c : in out conjunto; name : in String) is
      f_entrada : File_Type;
      line : String(1..100);
      length : Natural;
   begin
      cvacio(c);
      Open(f_entrada,In_File,name);

      while not End_Of_File(f_entrada) loop
         Get_Line(f_entrada,line,length);
         tratarLinea(c,line,length);
      end loop;

      Close(f_entrada);
   end mappingFichero;


   -- PROCEDIMIENTO crearArboles QUE CREA ÁRBOLES DE UN SOLO ELEM node CON LAS
   -- DUPLAS CLAVE-VALOR DEL MAPPING PASADO POR PARÁMETRO Y QUE SE AÑADIRÁN
   -- A UNA COLA DE PRIORIDAD
   procedure crearArboles(c : in conjunto; colaPrio : in out priority_queue) is
      it : iterador;
      nodo : node;
      pa,pa_aux : parbol;
      alfa : alfabet;
      int : Integer;
   begin
      primero(c,it);
      empty(colaPrio);
      pa_aux := new arbol;
      while es_valido(it) loop
         pa := new arbol;
         obtener(c,it,alfa,int);
         nodo := (alfa,int);
         graft(pa.all,pa_aux.all,pa_aux.all,nodo);
         put(colaPrio,pa);
         siguiente(c,it);
      end loop;
   end crearArboles;


   -- PROCEDIMIENTO crearHuffman QUE GENERA EL ÁRBOL DE HUFFMAN CORRESPONDIENTE
   -- A LOS ELEMENTOS parbol CONTENIDOS EN LA COLA DE PRIORIDAD PASADA POR
   -- PARÁMETRO Y QUE DEVOLVERÁ EL ÁRBOL GENERADO SOBRE EL PUNTERO PASADO POR PARÁMETRO
   procedure crearHuffman(colaPrio : in out priority_queue; pa : in out parbol) is
      nodo1,nodo2,nodoUnion : node;
      pa2 : parbol;
   begin
      pa := new arbol;
      while not is_empty(colaPrio) loop
         -- Extraer el elemento con menos frecuencia
         pa := get_least(colaPrio);
         delete_least(colaPrio);
         if not is_empty(colaPrio) then
            -- Contenia dos elementos (o más)
            pa2 := get_least(colaPrio);
            delete_least(colaPrio);

            raiz(pa.all,nodo1);
            raiz(pa2.all,nodo2);
            nodoUnion := ('-',nodo1.frequencia+nodo2.frequencia);
            graft(pa.all,pa.all,pa2.all,nodoUnion);

            put(colaPrio,pa);
         end if;
      end loop;
   end crearHuffman;

   -- PROCEDIMIENTO generarCodigo QUE REALIZA UNA BÚSQUEDA EN PREORDEN DEL ARBOL
   -- PASADO POR PARÁMETRO Y SE DEVUELVE SU CÓDGIO BINARIO ASOCIADO
   procedure generarCodigo(x : in parbol; caracter : in Character; trobat : in out Boolean; idx : in Integer; codi : in out tcodi) is
      -- codi se encuentra formado por :
      -- c: array de caracteres (0, 1)
      -- l: natural que indica la longitud del codigo
      pl, pr : parbol;
      nodo : node;
   begin
      -- visitar nodo consiste en :
      -- comprobar si la raiz del arbol contiene el caracter
      raiz(x.all,nodo);
      if (nodo.caracter = caracter) then
         trobat := True;
      end if;

      if not trobat then
         -- Si no se ha encontrado el caracteer:
         -- Bajar hacia el hijo izquierdo y añadir un '0'
         pl := new arbol;
         izq(x.all,pl.all);
         if not esta_vacio(pl.all) then
            codi.c(idx) := '0';
            codi.l := idx;
            generarCodigo(pl, caracter, trobat, idx+1, codi);
         end if;

         -- Si no se ha encontrado el caracter:
         -- Bajar hacia el hijo derecho y añadir un '1'
         pr := new arbol;
         der(x.all,pr.all);
         if not esta_vacio(pr.all) and not trobat then
            codi.c(idx) := '1';
            codi.l := idx;
            generarCodigo(pr, caracter, trobat, idx+1, codi);
         end if;
      end if;
   end generarCodigo;

   -- PROCEDIMIENTO grabarCodigo QUE COMPRUEBA QUE CARACTERES TIPO alfabet
   -- ESTÁN PRESENTES EN EL CONJUNTO Y GENERA UN FICHERO CON DICHOS CARACTERES
   -- DEL TEXTO ORDENADOS EN ORDEN ALFABÉTICO JUNTO CON SU CÓDIGO BINARIO CORRESPONDIENTE
   procedure grabarCodigo(c : in conjunto; pa : in parbol; name : in String) is
      f_salida : File_Type;
      it : iterador;
      alfa : alfabet;
      int, idx : Integer;
      code : tcodi;
      existe,trobat : Boolean;
      lineaCod : String(1..25);
   begin
      Create(f_salida, Out_File,name);
      for alfa_aux in alfabet'Range loop
         -- busqueda del caracter alfabet dentro del conjunto
         primero(c,it);
         existe := False;
         while es_valido(it) and not existe loop
            obtener(c,it,alfa,int);
            if (alfa = alfa_aux) then existe := True; end if;
            siguiente(c,it);
         end loop;

         -- si el caracter alfabet ha sido encontrado, generamos su codigo y lo
         -- grabamos en fichero
         if existe then
            trobat := False;
            idx := 1;
            generarCodigo(pa,alfa,trobat,idx,code);
            for i in 1..code.l loop
               lineaCod(i) := codigo(code.c(i));
            end loop;
            Put_Line(f_salida,alfa & ": " & lineaCod(1..code.l));
         end if;
      end loop;

      Close(f_salida);
   end grabarCodigo;


begin
   -- ACCIONES
   mappingFichero(c,"entrada.txt");
   crearArboles(c,colaP);
   crearHuffman(colaP,paUnion);
   grabarCodigo(c,paUnion, "entrada_codi.txt");
end Huffman;
