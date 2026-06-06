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
module FsOmegaLib.ARA


open System
open System.IO

open SAT
open AutomatonSkeleton
open AbstractAutomaton
open NBA

exception private NotWellFormedException of string

// The accepting type "reachability" is not part of HOA format. We transform the ARA into a büchi automaton for communication with spot. The reachability states are just büchi states. Internally we assume that, in a reachability automaton, each accepting state is terminal!
type ARA<'T, 'L when 'T : comparison and 'L : comparison> =
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


module ARA =
    let actuallyUsedAPs (ara : ARA<'T, 'L>) =
        AlternatingAutomatonSkeleton.actuallyUsedAPs ara.Skeleton

    let convertStatesToInt (ara : ARA<'T, 'L>) =
        let idDict = ara.Skeleton.States |> Seq.mapi (fun i x -> x, i) |> Map.ofSeq
        {
            ARA.Skeleton = ara.Skeleton |> AlternatingAutomatonSkeleton.mapStates (fun x -> idDict.[x])

            InitialStates = ara.InitialStates |> Set.map (Set.map (fun x -> idDict.[x]))
            AcceptingStates = ara.AcceptingStates |> Set.map (fun x -> idDict.[x])
        }

    let mapAPs (f : 'L -> 'U) (ara : ARA<'T, 'L>) =
        {
            Skeleton = AlternatingAutomatonSkeleton.mapAPs f ara.Skeleton
            InitialStates = ara.InitialStates
            AcceptingStates = ara.AcceptingStates
        }

    let trueAutomaton () : ARA<int, 'L> =
        {
            ARA.Skeleton =
                {
                    AlternatingAutomatonSkeleton.States = set ([ 0 ])
                    APs = []
                    Edges = [ 0, [ DNF.trueDNF, Set.singleton 0 ] ] |> Map.ofList
                }
            InitialStates = Set.singleton (Set.singleton 0)
            AcceptingStates = Set.singleton 0
        }

    let falseAutomaton () : ARA<int, 'L> =
        {
            ARA.Skeleton =
                {
                    States = set ([ 0 ])
                    APs = []
                    Edges = [ 0, List.empty ] |> Map.ofList
                }
            InitialStates = Set.singleton (Set.singleton 0)
            AcceptingStates = Set.empty
        }

    let toHoaString (stateStringer : 'T -> string) (alphStringer : 'L -> string) (labelStringer : 'T -> string)(aba : ARA<'T, 'L>) =
        (aba :> AbstractAutomaton<'T, 'L>).ToHoaString stateStringer alphStringer labelStringer

    let findError (aba : ARA<'T, 'L>) =
        (aba :> AbstractAutomaton<'T, 'L>).FindError()

    let bringToSameAPs (autList : list<ARA<'T, 'L>>) =
        autList
        |> List.map (fun x -> x.Skeleton)
        |> AlternatingAutomatonSkeleton.bringSkeletonsToSameAps
        |> List.mapi (fun i x -> { autList.[i] with Skeleton = x })

    let bringPairToSameAPs (ara1 : ARA<'T, 'L>) (ara2 : ARA<'T, 'L>) =
        let sk1, sk2 =
            AlternatingAutomatonSkeleton.bringSkeletonPairToSameAps ara1.Skeleton ara2.Skeleton

        { ara1 with Skeleton = sk1 }, { ara2 with Skeleton = sk2 }
    let addAPs (aps : list<'L>) (ara : ARA<'T, 'L>) =
        { ara with
            Skeleton = AlternatingAutomatonSkeleton.addAPsToSkeleton aps ara.Skeleton
        }

    let fixAPs (aps : list<'L>) (ara : ARA<'T, 'L>) =
        { ara with
            Skeleton = AlternatingAutomatonSkeleton.fixAPsToSkeleton aps ara.Skeleton
        }

    let projectToTargetAPs (newAPs : list<'L>) (ara : ARA<'T, 'L>) =
        { ara with
            Skeleton = AlternatingAutomatonSkeleton.projectToTargetAPs newAPs ara.Skeleton
        }

    let computeBisimulationQuotient (ara : ARA<'T, 'L>) =
        let bisimSkeleton, m =
            AutomatonSkeleton.AlternatingAutomatonSkeleton.computeBisimulationQuotient
                (fun x -> Set.contains x ara.AcceptingStates)
                ara.Skeleton

        {
            ARA.Skeleton = bisimSkeleton
            InitialStates = ara.InitialStates |> Set.map (Set.map (fun x -> m.[x]))
            AcceptingStates = ara.AcceptingStates |> Set.map (fun x -> m.[x])
        }
