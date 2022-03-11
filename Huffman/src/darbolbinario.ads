--------------------------------------------------------------------------------
-- SOURCE ÁRBOL BINARIO
--------------------------------------------------------------------------------
-- Utilizaremos esta implementación formar el Árbol de Huffman, el que tendrá
-- nodos carácter-frecuencia
--------------------------------------------------------------------------------
generic
   type elem is private ;
package darbolbinario is
   type arbol is limited private ;

   mal_uso : exception ;
   espacio_desbordado : exception ;

   procedure avacio ( t : out arbol ) ;
   function esta_vacio ( t : in arbol ) return boolean ;
   procedure graft ( t : out arbol ; lt , rt : in arbol ; x : in elem ) ;
   procedure raiz ( t : in arbol ; x : out elem ) ;
   procedure izq ( t : in arbol ; lt : out arbol ) ;
   procedure der ( t : in arbol ; rt : out arbol ) ;
private
   type nodo;
   type pnodo is access nodo;
   type nodo is record
      x: elem;
      l, r: pnodo;
   end record;
   type arbol is record
      raiz: pnodo;
   end record;
end darbolbinario ;
