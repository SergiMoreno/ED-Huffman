--------------------------------------------------------------------------------
-- SOURCE CONJUNTO
--------------------------------------------------------------------------------
-- Utilizaremos esta implementación con iterador de un array indexado por claves
-- para representar que claves del tipo alfabet se encuentran presentes en el
-- texto de un fichero y almacenaremos su valor de frecuencia de aparición
--------------------------------------------------------------------------------
generic
   -- tipo discreto
   type key is (<>);
   type item is private;
package d_conjunto is
   type conjunto is limited private;
   ya_existe: exception;
   no_existe: exception;
   espacio_desbordado: exception;
   procedure cvacio (s: out conjunto);
   procedure poner (s: in out conjunto; k: in key; x: in item);
   procedure consultar(s: in conjunto; k: in key; x: out item);
   procedure borrar(s: in out conjunto; k: in key);
   procedure actualiza(s: in out conjunto; k: in key; x: in item);

   type iterador is private;
   mal_uso : exception;
   procedure primero(s: in conjunto; it: out iterador );
   procedure siguiente(s: in conjunto; it: in out iterador );
   function es_valido (it: in iterador ) return boolean;
   procedure obtener(s: in conjunto; it: in iterador ; k: out key; x: out item);
private
   type existencia is array(key) of boolean;
   type contenido is array(key) of item;
   type conjunto is record
      e: existencia;
      c: contenido;
   end record;
   type iterador is record
      k: key;
      valid : boolean;
   end record;
end d_conjunto;
