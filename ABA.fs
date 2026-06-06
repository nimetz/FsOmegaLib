(*    
    Copyright (C) 2025-2026 Niklas Metzger

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
*)
module FsOmegaLib.ABA


open System
open System.IO

open SAT
open AutomatonSkeleton
open AbstractAutomaton
open DPA
open NBA

exception private NotWellFormedException of string

type ABA<'T, 'L when 'T : comparison and 'L : comparison> =
    {
        Skeleton : AlternatingAutomatonSkeleton<'T, 'L>
        InitialStates : Set<Set<'T>>
        AcceptingStates : Set<'T>
    }

    member this.States = this.Skeleton.States

    member this.Edges = this.Skeleton.Edges

    member this.APs = this.Skeleton.APs

    interface AbstractAutomaton<'T, 'L> with
        member this.Skeleton = this.Skeleton

        member this.FindError() =
            try
                match AlternatingAutomatonSkeleton.findError this.Skeleton with
                | Some err -> raise <| NotWellFormedException err
                | None -> ()

                this.InitialStates
                |> Set.iter (
                    Set.iter (fun x ->
                        if this.Skeleton.States.Contains x |> not then
                            raise
                            <| NotWellFormedException $"The initial state %A{x} is not contained in the set of states"
                    )
                )

                this.AcceptingStates
                |> Seq.iter (fun x ->
                    if this.Skeleton.States.Contains x |> not then
                        raise
                        <| NotWellFormedException $"State $A{x} is accepting but not contained in the set of states"
                )

                None
            with NotWellFormedException msg ->
                Some msg

        member this.ToHoaString (stateStringer : 'T -> string) (alphStringer : 'L -> string) (labelStringer : 'T -> string)=
            let stringWriter = new StringWriter()

            stringWriter.WriteLine("HOA: v1")

            stringWriter.WriteLine("States: " + string this.States.Count)

            for s in this.InitialStates do
                let c = s |> Set.toList |> List.map stateStringer |> String.concat " & "

                stringWriter.WriteLine("Start: " + c)

            let apsString =
                this.APs
                |> List.map (fun x -> "\"" + alphStringer (x) + "\"")
                |> String.concat " "

            stringWriter.WriteLine("AP: " + string (this.APs.Length) + " " + apsString)

            stringWriter.WriteLine("acc-name: Buchi")
            stringWriter.WriteLine("Acceptance: 1 Inf(0)")


            stringWriter.WriteLine "--BODY--"

            let accCondition s =
                if this.AcceptingStates.Contains s then "{0}" else ""

            stringWriter.WriteLine(
                AlternatingAutomatonSkeleton.printBodyInHanoiFormat stateStringer accCondition labelStringer this.Skeleton
            )

            stringWriter.WriteLine "--END--"

            stringWriter.ToString()


module ABA =
    let actuallyUsedAPs (aba : ABA<'T, 'L>) =
        AlternatingAutomatonSkeleton.actuallyUsedAPs aba.Skeleton

    let convertStatesToInt (aba : ABA<'T, 'L>) =
        let idDict = aba.Skeleton.States |> Seq.mapi (fun i x -> x, i) |> Map.ofSeq

        {
            ABA.Skeleton = aba.Skeleton |> AlternatingAutomatonSkeleton.mapStates (fun x -> idDict.[x])

            InitialStates = aba.InitialStates |> Set.map (Set.map (fun x -> idDict.[x]))

            AcceptingStates = aba.AcceptingStates |> Set.map (fun x -> idDict.[x])
        }


    let fromNBA (nba : NBA<'T, 'L>) =
        {
            ABA.Skeleton = nba.Skeleton |> NondeterministicAutomatonSkeleton.toAlternatingAutomatonSkeleton
            InitialStates = nba.InitialStates |> Set.singleton
            AcceptingStates = nba.AcceptingStates
        }

    let mapAPs (f : 'L -> 'U) (aba : ABA<'T, 'L>) =
        {
            Skeleton = AlternatingAutomatonSkeleton.mapAPs f aba.Skeleton
            InitialStates = aba.InitialStates
            AcceptingStates = aba.AcceptingStates
        }

    let trueAutomaton () : ABA<int, 'L> =
        {
            ABA.Skeleton =
                {
                    AlternatingAutomatonSkeleton.States = set ([ 0 ])
                    APs = []
                    Edges = [ 0, [ DNF.trueDNF, Set.singleton 0 ] ] |> Map.ofList
                }
            InitialStates = Set.singleton (Set.singleton 0)
            AcceptingStates = Set.singleton 0
        }

    let falseAutomaton () : ABA<int, 'L> =
        {
            ABA.Skeleton =
                {
                    States = set ([ 0 ])
                    APs = []
                    Edges = [ 0, List.empty ] |> Map.ofList
                }
            InitialStates = Set.singleton (Set.singleton 0)
            AcceptingStates = Set.empty
        }

    let toHoaString (stateStringer : 'T -> string) (alphStringer : 'L -> string) (labelStringer : 'T -> string)(aba : ABA<'T, 'L>) =
        (aba :> AbstractAutomaton<'T, 'L>).ToHoaString stateStringer alphStringer labelStringer

    let findError (aba : ABA<'T, 'L>) =
        (aba :> AbstractAutomaton<'T, 'L>).FindError()

    let bringToSameAPs (autList : list<ABA<'T, 'L>>) =
        autList
        |> List.map (fun x -> x.Skeleton)
        |> AlternatingAutomatonSkeleton.bringSkeletonsToSameAps
        |> List.mapi (fun i x -> { autList.[i] with Skeleton = x })

    let bringPairToSameAPs (aba1 : ABA<'T, 'L>) (aba2 : ABA<'T, 'L>) =
        let sk1, sk2 =
            AlternatingAutomatonSkeleton.bringSkeletonPairToSameAps aba1.Skeleton aba2.Skeleton

        { aba1 with Skeleton = sk1 }, { aba2 with Skeleton = sk2 }

    let addAPs (aps : list<'L>) (apa : ABA<'T, 'L>) =
        { apa with
            Skeleton = AlternatingAutomatonSkeleton.addAPsToSkeleton aps apa.Skeleton
        }

    let fixAPs (aps : list<'L>) (apa : ABA<'T, 'L>) =
        { apa with
            Skeleton = AlternatingAutomatonSkeleton.fixAPsToSkeleton aps apa.Skeleton
        }

    let projectToTargetAPs (newAPs : list<'L>) (aba : ABA<'T, 'L>) =
        { aba with
            Skeleton = AlternatingAutomatonSkeleton.projectToTargetAPs newAPs aba.Skeleton
        }

    let computeBisimulationQuotient (aba : ABA<'T, 'L>) =
        let bisimSkeleton, m =
            AutomatonSkeleton.AlternatingAutomatonSkeleton.computeBisimulationQuotient
                (fun x -> Set.contains x aba.AcceptingStates)
                aba.Skeleton

        {
            ABA.Skeleton = bisimSkeleton
            InitialStates = aba.InitialStates |> Set.map (Set.map (fun x -> m.[x]))
            AcceptingStates = aba.AcceptingStates |> Set.map (fun x -> m.[x])
        }
