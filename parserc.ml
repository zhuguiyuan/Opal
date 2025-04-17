(* I write this file to learn parser combinator. I have first tries.
 * Then I refer to https://github.com/pyrocat101/opal to improve the code.
 *   (also see the document in that repository)
 * The impl finally layers as basic, monoid, functor, applicative and monad.
 * Zhu Guiyuan (2025) 951620305@qq.com  *)

module Parserc = struct
  (* Type *)
  type ('token, 'value) parser =
    | Parser of ('token list -> ('value * 'token list) option)

  let run (Parser p) s = p s
  let parse p s = match run p s with Some (x, _) -> Some x | None -> None

  (* Basic *)
  let empty = Parser (fun s -> Some ((), s))
  let any = Parser (function hd :: tl -> Some (hd, tl) | [] -> None)

  let satisfy predicate =
    Parser
      (fun s ->
        match s with
        | x :: s' -> if predicate x then Some (x, s') else None
        | [] -> None)

  let eof x = Parser (function [] -> Some (x, []) | _ -> None)

  (* Monoid *)
  let fail = Parser (fun _ -> None)

  let ( <|> ) (Parser px) (Parser py) =
    Parser (fun s -> match px s with Some _ as x -> x | None -> py s)

  let rec choice = function [] -> fail | hd :: tl -> hd <|> choice tl

  (* Functor *)
  let fmap f (Parser p) =
    Parser (fun s -> Option.map (fun (fst, snd) -> (f fst, snd)) (p s))

  let ( => ) p f = fmap f p
  let fst p = p => fun (a, b) -> a
  let snd p = p => fun (a, b) -> b

  (* Applicative Functor *)
  let pure x = Parser (fun s -> Some (x, s))
  let option default p = p <|> pure default
  let optional p = option () p

  let ( <*> ) pf p =
    Parser
      (fun s ->
        Option.bind (run pf s) (fun (f, s') ->
            Option.bind (run p s') (fun (x, s'') -> Some (f x, s''))))

  let liftA2 f px py = pure f <*> px <*> py
  let ( <&> ) px py = liftA2 (fun a b -> (a, b)) px py
  let ( *> ) px py = px <&> py |> snd
  let ( <* ) px py = px <&> py |> fst
  let between left right p = left *> p <* right
  let ( <~> ) px pxs = liftA2 (fun a b -> a :: b) px pxs

  let traverseA f ps =
    let cons = liftA2 (fun x xs -> f x :: xs) in
    List.fold_right cons ps (pure [])

  let forA ps f = traverseA f ps
  let sequenceA ps = traverseA (fun x -> x) ps
  let replicateM n p = sequenceA (List.init n (fun _ -> p))
  let rec skip_many p = Parser (fun s -> run (optional (p *> skip_many p)) s)
  let skip_many1 p = p *> skip_many p
  let rec many p = Parser (fun s -> run (option [] (p <~> many p)) s)
  let many1 p = p <~> many p
  let sep_by1 p sep = p <~> many (sep *> p)
  let sep_by p sep = sep_by1 p sep <|> pure []
  let end_by1 p sep = sep_by1 p sep <* sep
  let end_by p sep = end_by1 p sep <|> pure []

  let chainl1 p op =
    let combine (x, ops) = List.fold_left (fun acc (f, y) -> f acc y) x ops in
    p <&> many (op <&> p) => combine

  let chainl p op default = chainl1 p op <|> pure default

  let chainr1 p op =
    let combine (x, ops) = List.fold_left (fun acc (f, y) -> f y acc) x ops in
    p <&> many (op <&> p) => combine

  let chainr p op default = chainr1 p op <|> pure default

  (* Monad *)
  let ( >>= ) p f =
    Parser (fun s -> Option.bind (run p s) (fun (a, s') -> run (f a) s'))

  let ( let* ) = ( >>= )
  (* WOW we just use applicative to impl most things and without monad! *)

  (* Singletons *)
  let exactly x = satisfy (( = ) x)
  let one_of xs = satisfy (fun x -> List.mem x xs)
  let none_of xs = satisfy (fun x -> not (List.mem x xs))
  let range l r = satisfy (fun x -> l <= x && x <= r)

  (* Char Parsers *)
  let space = one_of [ ' '; '\t'; '\r'; '\n' ]
  let spaces = skip_many space
  let newline = exactly '\n'
  let tab = exactly '\t'
  let upper = range 'A' 'Z'
  let lower = range 'a' 'z'
  let digit = range '0' '9'
  let letter = lower <|> upper
  let alpha_num = letter <|> digit
  let hex_digit = range 'a' 'f' <|> range 'A' 'F' <|> digit
  let oct_digit = range '0' '7'

  (* Helpers *)
  let of_lazy pl = Parser (fun s -> run (Lazy.force pl) s)

  let rec scan p =
   fun input ->
    match run p input with Some (v, tl) -> v :: scan p tl | None -> []

  let lexeme p = spaces *> p

  let string s =
    let len = String.length s in
    let check =
      Parser
        (fun input ->
          let rec aux i = function
            | [] when i = len -> Some (s, [])
            | c :: tl when i < len && c = String.get s i -> aux (i + 1) tl
            | _ -> None
          in
          aux 0 input)
    in
    lexeme check

  let string_of_chars cs = String.of_seq (List.to_seq cs)
  let chars_of_string s = List.of_seq (String.to_seq s)
  let ( >> ) f g = fun x -> g (f x)
  let ( << ) f g = fun x -> f (g x)
end

module Test = struct
  open Parserc

  type expr =
    | Num of int
    | Add of expr * expr
    | Sub of expr * expr
    | Mul of expr * expr
    | Div of expr * expr

  let parens p = between (exactly '(') (exactly ')') p

  let integer =
    many1 digit => (string_of_chars >> int_of_string) => fun a -> Num a

  let add = exactly '+' *> pure (fun a b -> Add (a, b))
  let sub = exactly '-' *> pure (fun a b -> Sub (a, b))
  let mul = exactly '*' *> pure (fun a b -> Mul (a, b))
  let div = exactly '/' *> pure (fun a b -> Div (a, b))

  let rec expr = Parser (fun input -> run (chainl1 term (add <|> sub)) input)
  and term = Parser (fun input -> run (chainl1 factor (mul <|> div)) input)
  and factor = Parser (fun input -> run (parens expr <|> integer) input)

  let x = run expr (chars_of_string "(1+233*(3-2-1))")

  let foo =
    let* _ = exactly '(' in
    let* x = integer in
    let* _ = exactly ')' in
    pure x

  let y = run foo (chars_of_string "(10)")
  let z = run spaces (chars_of_string "    a")
end
