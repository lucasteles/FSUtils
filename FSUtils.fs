[<AutoOpen>]
module FSUtils

open System.Collections.Concurrent
open System.Collections.Generic
open System
open System.Linq
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Linq.RuntimeHelpers
open System.Linq.Expressions

[<AutoOpen>]
module Common =
    let ever x _ = x
    let flip f = fun a b -> f b a
    let curry f = fun a1 a2 -> f (a1, a2)
    let curry3 f = fun a1 a2 a3 -> f (a1, a2, a3)
    let curry4 f = fun a1 a2 a3 a4 -> f (a1, a2, a3, a4)

    let curry5 f =
        fun a1 a2 a3 a4 a5 -> f (a1, a2, a3, a4, a5)

    let rec until p f x = if p x then x else until p f (f x)
    let evenf n = n % 2. = 0.
    let evenf32 n = n % 2f = 0f
    let even n = n % 2 = 0
    let odd n = n % 2 = 0
    let oddf n = n % 2. = 0.
    let oddf32 n = n % 2f = 0f
    let inline rem a b = a % b
    let inline modulo n m =
        let mod' = n % m
        if sign mod' >= 0 then mod' else abs m + mod'

    let inline private gcdbase zero x y =
        let rec gcd' x y =
            match x, y with
            | x, y when y = zero -> x
            | x, y -> gcd' y (x % y)

        gcd' (abs x) (abs y)

    let gcd x y = gcdbase 0 x y
    let gcdf x y = gcdbase 0. x y
    let gcdf32 x y = gcdbase 0f x y

    let lcm x y =
        match x,y with
        | _,0 | 0,_ -> 0
        | x, y -> abs ((Math.DivRem(x, gcd x y) |> fst ) * y)

    let inc n = n+1
    let dec n = n-1
    let subtract = flip (-)

    let complement f = f >> not
    let same a b = Object.ReferenceEquals(a,b)
    let iif cond a b = if cond then a else b
    let unless cond a b = if not cond then a else b
    let juxt f g param = f param, g param
    let juxt3 f g h param = f param, g param, h param
    let identity n = n
    let identity2 _ n = n
    let inline pos n = sign n > 0
    let inline neg n = sign n < 0
    let inline zero n = sign n = 0
    let isGuid n = Guid.TryParse((n : string)) |> fst

    let memoize f =
        let cache = Dictionary<_,_>()
        fun c ->
            match cache.TryGetValue c with
            | true, value -> value
            | _ ->
                let value = f c
                cache.Add (c, value)
                value

    let memoize2 f =
        let cache = Dictionary<_,_>()
        fun c d ->
            let key = c,d
            match cache.TryGetValue key with
            | true, value -> value
            | _ ->
                let value = f c d
                cache.Add ((c,d), value)
                value

    let memoizeSafe f =
        let cache = ConcurrentDictionary<_,_>()
        fun c ->
            match cache.TryGetValue c with
            | true, value -> value
            | _ ->
                let value = f c
                cache.AddOrUpdate(c, value, fun _ b -> b)
                value

    let memoizeSafe2 f =
        let cache = ConcurrentDictionary<_,_>()
        fun c d ->
            let key = c,d
            match cache.TryGetValue key with
            | true, value -> value
            | _ ->
                let value = f c d
                cache.AddOrUpdate((c,d), value, fun _ b -> b)
                value
module Seq =

    let asReadOnly col = col |> Seq.toArray :> IReadOnlyCollection<_>
    let interleave c1 c2 =
        Seq.zip c1 c2
        |> Seq.collect (fun (a, b) -> [ a; b ])

    let interleave3 c1 c2 c3 =
        Seq.zip3 c1 c2 c3
        |> Seq.collect (fun (a, b, c) -> [ a; b; c ])

    let any col = col |> Seq.isEmpty |> not

    let chunck number col =
        seq {
            let list = List<_>()

            for v in col do
                if list |> Seq.length |> (=) number then
                    list |> List.ofSeq
                    list.Clear()

                list.Add(v)

            if any list then list |> List.ofSeq
        }

    // Return all the elements of a list except the last one. The list must be non-empty.
    let beginning (col: 'a seq) =
        let enumerator = col.GetEnumerator()

        let rec loop (value: 'a) =
            if enumerator.MoveNext() then
                seq {
                    value
                    yield! loop enumerator.Current
                }
            else
                Seq.empty

        enumerator.MoveNext() |> ignore
        enumerator.Current |> loop

    //The intersperse function takes an element and a list and `intersperses' that element between the elements of the list. For example,
    let intersperse (item: 'a) (col: 'a seq) =
        seq {
            for i in col do
                i
                item
        }
        |> beginning

    //intercalate xs xss is equivalent to (concat (intersperse xs xss)). It inserts the list xs in between the lists in xss and concatenates the result.
    let intercalate (items: 'a seq) (col: 'a seq seq) =
        col |> intersperse items |> Seq.collect id

    let and' col = Seq.forall id col
    let or' col = Seq.exists id col

    let inline product col = Seq.foldBack (*) col 1.
    let repeat x = seq {while true do yield x}

    let cycle col = repeat col |> Seq.collect id
    let intersect (a: _ seq) (b: _ seq) = a.Intersect(b) :> _ seq
    let union (a: _ seq) (b: _ seq) = a.Union(b) :> _ seq
    let except (a: _ seq) (b: _ seq) = a.Except(b) :> _ seq
    let add (item: 'a ) (col: 'a seq) = col.Append(item) :> _ seq
    let nub (col: 'a seq) = Set col |> Set.toSeq
    let delete (item: 'a) (col: 'a seq) =
        let mutable skipped = false
        seq { for v in col do
                  if v = item && not skipped
                  then skipped <- true
                  else v}
    let headhead col = col |> Seq.head |> Seq.head
    let tryHeadhead col = col |> Seq.tryHead |> Option.bind Seq.tryHead
module List =
    let rec beginning =
        function
        | []
        | [ _ ] -> []
        | x :: xs -> x :: (beginning xs)

    let rec span pred col =
        match col with
        | [] -> [], []
        | x::xs' as xs ->
            let (ys, zs) = span pred xs'
            if pred x then x::ys,zs else [],xs

    let cons item col = item :: col
    (* Decompose a list into its head and tail.
      If the list is empty, returns None.
      If the list is non-empty, returns Some (x, xs), where x is the head of the list and xs its tail. *)
    let uncons col =
        match col with
        | [] -> None
        | (x :: xs) -> Some(x, xs)

    // | The 'nonEmptySubsequences' function returns the list of all subsequences of the argument,
    //   except for the empty list.
    //
    // >>> nonEmptySubsequences "abc"
    // ["a";"b";"ab";"c";"ac";"bc";"abc"]
    let rec nonEmptySubsequences (col: 'a list) =
        match col with
        | [] -> []
        | x :: xs ->
            let f ys r = ys :: (x :: ys) :: r

            [ x ]
            :: List.foldBack f (nonEmptySubsequences xs) []

    // | The 'subsequences' function returns the list of all subsequences of the argument.
    //
    // >>> subsequences "abc"
    // ["";"a";"b";"ab";"c";"ac";"bc";"abc"]
    let subsequences (col: 'a list) = [] :: nonEmptySubsequences col

    let rec distribute e =
        function
        | [] -> [ [ e ] ]
        | x :: xs' as xs ->
            (e :: xs)
            :: [ for xs in distribute e xs' -> x :: xs ]

    let rec permutations =
        function
        | [] -> [ [] ]
        | e :: xs -> List.collect (distribute e) (permutations xs)

    let repeat x = [ while true do x ]

    let delete (item: 'a) (col: 'a list) =
        let rec loop skipped = function
            | [] -> []
            | x::xs  ->
                if x = item && not skipped
                then loop true xs
                else x :: loop skipped xs

        loop false col

module Tuple =

    let map f (a,b) = (f a, f b)
    let mapLeft f (a,b) = (f a, b)
    let mapRight f (a,b) = (a,f b)

module String =

    let ofChars (chars: char seq) =
        chars
        |> Seq.map string
        |> String.concat String.Empty

    let intercalate (inter: string) (texts: string seq) =
        texts
        |> Seq.cast<char seq>
        |> Seq.intercalate inter
        |> ofChars

    let nonEmptySubsequences (str: string) =
        str
        |> List.ofSeq
        |> List.nonEmptySubsequences
        |> List.map ofChars

    let subsequences (str: string) =
        String.Empty :: (nonEmptySubsequences str)

    let permutations (str: string) =
        str
        |> List.ofSeq
        |> List.permutations
        |> List.map ofChars

    let isEmpty str = String.IsNullOrEmpty(str)
    let isWhiteSpace str = String.IsNullOrWhiteSpace(str)
    let split (sep: char) (str: string) = str.Split(sep)
    let lines (str: string) = split '\n' str

    let span pred (str: string) =
        str
        |> List.ofSeq
        |> List.span pred
        |> Tuple.map ofChars

    let unlines strs = String.concat "\n" strs
    let unwords strs = String.concat " " strs
    let words str =
        str |> lines |> Array.collect (split ' ') |> List.ofArray |> List.filter (String.IsNullOrWhiteSpace >> not)

module Expr =
    let toLinq (expr : Expr<'a -> 'b>) =
      let linq = LeafExpressionConverter.QuotationToExpression expr
      let call = linq :?> MethodCallExpression
      let lambda = call.Arguments.[0] :?> LambdaExpression
      Expression.Lambda<Func<'a, 'b>>(lambda.Body, lambda.Parameters)

module DateTime =
    let add(value: TimeSpan, date: DateTime ) = date.Add(value)
    let addDays(value: double, date: DateTime ) = date.AddDays (value)
    let addHours(value: double, date: DateTime ) = date.AddHours (value)
    let addMilliseconds(value: double, date: DateTime ) = date.AddMilliseconds (value)
    let addMinutes(value: double, date: DateTime ) = date.AddMinutes (value)
    let addMonths(months: int, date: DateTime ) = date.AddMonths (months)
    let addSeconds(value: double, date: DateTime ) = date.AddSeconds (value)
    let addTicks(value: int64, date: DateTime ) = date.AddTicks (value)
    let addYears(value: int, date: DateTime ) = date.AddYears (value)
    let date(date: DateTime) = date.Date
    let kind(date: DateTime) = date.Kind
    let subtract(value: TimeSpan, date: DateTime ) = date.Subtract (value)
    let toLocalTime (date: DateTime) = date.ToLocalTime()
    let toUniversalTime (date: DateTime) = date.ToUniversalTime()
    let day (date: DateTime) = date.Day
    let DayOfWeek (date: DateTime) = date.DayOfWeek
    let hour (date: DateTime) = date.Hour
    let second (date: DateTime) = date.Second
    let minute (date: DateTime) = date.Minute
    let millisecond (date: DateTime) = date.Millisecond
    let month (date: DateTime) = date.Month
    let year (date: DateTime) = date.Year
    let ticks (date: DateTime) = date.Ticks
    let dayOfYear (date: DateTime) = date.DayOfYear
    let timeOfDay (date: DateTime) = date.TimeOfDay


module DateTimeOffset =
    let add(value: TimeSpan, date: DateTimeOffset ) = date.Add(value)
    let addDays(value: double, date: DateTimeOffset ) = date.AddDays (value)
    let addHours(value: double, date: DateTimeOffset ) = date.AddHours (value)
    let addMilliseconds(value: double, date: DateTimeOffset ) = date.AddMilliseconds (value)
    let addMinutes(value: double, date: DateTimeOffset ) = date.AddMinutes (value)
    let addMonths(months: int, date: DateTimeOffset ) = date.AddMonths (months)
    let addSeconds(value: double, date: DateTimeOffset ) = date.AddSeconds (value)
    let addTicks(value: int64, date: DateTimeOffset ) = date.AddTicks (value)
    let addYears(value: int, date: DateTimeOffset ) = date.AddYears (value)
    let date(date: DateTimeOffset) = date.Date
    let offset(date: DateTimeOffset) = date.Offset
    let subtract(value: TimeSpan, date: DateTimeOffset ) = date.Subtract (value)
    let toLocalTime (date: DateTimeOffset) = date.ToLocalTime()
    let toUniversalTime (date: DateTimeOffset) = date.ToUniversalTime()
    let day (date: DateTimeOffset) = date.Day
    let DayOfWeek (date: DateTimeOffset) = date.DayOfWeek
    let hour (date: DateTimeOffset) = date.Hour
    let second (date: DateTimeOffset) = date.Second
    let minute (date: DateTimeOffset) = date.Minute
    let millisecond (date: DateTimeOffset) = date.Millisecond
    let month (date: DateTimeOffset) = date.Month
    let year (date: DateTimeOffset) = date.Year
    let ticks (date: DateTimeOffset) = date.Ticks
    let dayOfYear (date: DateTimeOffset) = date.DayOfYear
    let timeOfDay (date: DateTimeOffset) = date.TimeOfDay

module vai =
    Seq.intersperse "|" [ "a"; "b"; "c" ]
    |> Seq.beginning
    |> List.ofSeq

    [ 1; 2; 3 ] |> Seq.beginning
    [ 1; 2; 3; 4 ] |> Seq.beginning
    [ 1 ] |> Seq.beginning
    [] |> Seq.beginning
    [ 1; 2; 3; 4; 5 ] |> Seq.chunck 2
    String.nonEmptySubsequences "abc"

    List.permutations [ 1; 2; 3 ]
    String.permutations "abc"

    Seq.product []
    String.span Char.IsDigit "123abc456"

    String.unlines ["hello world"; "it's me,"; "eric"]

    String.words "the quick brown\n\nfox"
    Seq.nub [1;2;3;4;3;2;1;2;4;3;5]
    List.delete 3 [1;2;3;4;1;3;4]
