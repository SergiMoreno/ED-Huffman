--------------------------------------------------------------------------------
-- BODY ÁRBOL BINARIO
--------------------------------------------------------------------------------
package body darbolbinario is

   procedure avacio(t: out arbol) is
      p: pnodo renames t.raiz;
   begin
      p:= null;
   end avacio;

   function esta_vacio(t: in arbol) return boolean is
      p: pnodo renames t.raiz;
   begin
      return p=null;
   end esta_vacio;

   procedure graft(t: out arbol; lt, rt: in arbol; x: in elem) is
      p: pnodo renames t.raiz;
      pl: pnodo renames lt.raiz;
      pr: pnodo renames rt.raiz;
   begin
      p:= new nodo;
      p.all:= (x, pl, pr);
   exception
      when storage_error => raise espacio_desbordado;
   end graft;

   procedure raiz(t: in arbol; x: out elem) is
      p: pnodo renames t.raiz;
   begin
      x:= p.x;
   exception
      when constraint_error => raise mal_uso;
   end raiz;

   procedure izq(t: in arbol; lt: out arbol) is
      p: pnodo renames t.raiz;
      pl: pnodo renames lt.raiz;
   begin
      pl:= p.l;
   exception
      when constraint_error => raise mal_uso;
   end izq;

   procedure der(t: in arbol; rt: out arbol) is
      p: pnodo renames t.raiz;
      pr: pnodo renames rt.raiz;
   begin
      pr:= p.r;
   exception
      when constraint_error => raise mal_uso;
   end der;
end darbolbinario;
