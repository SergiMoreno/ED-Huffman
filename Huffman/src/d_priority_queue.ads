--------------------------------------------------------------------------------
-- SOURCE HEAP
--------------------------------------------------------------------------------
-- Utilizaremos esta implementación ordenar los árboles binarios de un solo nodo
-- carácter-frecuencia. En el main definiremos el orden de prioridad, estable-
-- -ciendo a los carácteres con menor frecuencia como los más prioritarios
--------------------------------------------------------------------------------
generic
   -- tamano maximo de la cola de prioridad
   size : positive ;
   -- tipo de elementos que contendra la cola de prioridad
   type item is private ;
   -- funcion que devuelve si el item x1 es menor que el item x2
   with function "<" ( x1 , x2 : in item ) return boolean ;
   -- funcion que devuelve si el item x1 es mayor que el item x2
   with function ">" ( x1 , x2 : in item ) return boolean ;
package d_priority_queue is
   type priority_queue is limited private;

   space_overflow: exception;
   bad_use: exception;

   procedure empty (q : out priority_queue);
   procedure put (q : in out priority_queue; x : in item);
   procedure delete_least (q : in out priority_queue);
   function get_least (q : in priority_queue) return item;
   function is_empty (q: in priority_queue) return boolean;
private
   type mem_space is array (1..size) of item;
   type priority_queue is record
      a: mem_space;
      n: natural;
   end record;
end d_priority_queue;
