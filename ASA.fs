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

module FsOmegaLib.ASA


open System
open System.IO

open SAT
open AutomatonSkeleton
open AbstractAutomaton
open DPA
open NSA

exception private NotWellFormedException of string

// We assume that all states are accepting unless stated otherwise.
type ASA<'T, 'L when 'T : comparison and 'L : comparison> =
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

            if this.AcceptingStates = this.Skeleton.States then
                stringWriter.WriteLine("acc-name: all")

                stringWriter.WriteLine("Acceptance: 0 t")
            else
                stringWriter.WriteLine("acc-name: Buchi")
                stringWriter.WriteLine("Acceptance: 1 Inf(0)")



            stringWriter.WriteLine "--BODY--"

            let accCondition s =
                if this.AcceptingStates = this.Skeleton.States then 
                    ""
                else
                    if this.AcceptingStates.Contains s then "{0}" else ""

            stringWriter.WriteLine(
                AlternatingAutomatonSkeleton.printBodyInHanoiFormat stateStringer accCondition labelStringer this.Skeleton
            )

            stringWriter.WriteLine "--END--"

            stringWriter.ToString()


module ASA =
    let actuallyUsedAPs (asa : ASA<'T, 'L>) =
        AlternatingAutomatonSkeleton.actuallyUsedAPs asa.Skeleton

    let convertStatesToInt (asa : ASA<'T, 'L>) =
        let idDict = asa.Skeleton.States |> Seq.mapi (fun i x -> x, i) |> Map.ofSeq

        {
            ASA.Skeleton = asa.Skeleton |> AlternatingAutomatonSkeleton.mapStates (fun x -> idDict.[x])

            InitialStates = asa.InitialStates |> Set.map (Set.map (fun x -> idDict.[x]))
            AcceptingStates = asa.AcceptingStates |> Set.map (fun x -> idDict.[x])
        }


    let fromNSA (nsa : NSA<'T, 'L>) =
        {
            ASA.Skeleton = nsa.Skeleton |> NondeterministicAutomatonSkeleton.toAlternatingAutomatonSkeleton
            InitialStates = nsa.InitialStates |> Set.singleton
            AcceptingStates = nsa.Skeleton.States
        }

    let mapAPs (f : 'L -> 'U) (asa : ASA<'T, 'L>) =
        {
            Skeleton = AlternatingAutomatonSkeleton.mapAPs f asa.Skeleton
            InitialStates = asa.InitialStates
            AcceptingStates = asa.AcceptingStates
        }

    let trueAutomaton () : ASA<int, 'L> =
        {
            ASA.Skeleton =
                {
                    AlternatingAutomatonSkeleton.States = set ([ 0 ])
                    APs = []
                    Edges = [ 0, [ DNF.trueDNF, Set.singleton 0 ] ] |> Map.ofList
                }
            InitialStates = Set.singleton (Set.singleton 0)
            AcceptingStates = Set.singleton 0
        }

    let falseAutomaton () : ASA<int, 'L> =
        {
            ASA.Skeleton =
                {
                    States = set ([ 0 ])
                    APs = []
                    Edges = [ 0, List.empty ] |> Map.ofList
                }
            InitialStates = Set.singleton (Set.singleton 0)
            AcceptingStates = Set.empty
        }

    let toHoaString (stateStringer : 'T -> string) (alphStringer : 'L -> string) (labelStringer : 'T -> string)(asa : ASA<'T, 'L>) =
        (asa :> AbstractAutomaton<'T, 'L>).ToHoaString stateStringer alphStringer labelStringer
    let findError (asa : ASA<'T, 'L>) =
        (asa :> AbstractAutomaton<'T, 'L>).FindError()

    let bringToSameAPs (autList : list<ASA<'T, 'L>>) =
        autList
        |> List.map (fun x -> x.Skeleton)
        |> AlternatingAutomatonSkeleton.bringSkeletonsToSameAps
        |> List.mapi (fun i x -> { autList.[i] with Skeleton = x })

    let bringPairToSameAPs (asa1 : ASA<'T, 'L>) (asa2 : ASA<'T, 'L>) =
        let sk1, sk2 =
            AlternatingAutomatonSkeleton.bringSkeletonPairToSameAps asa1.Skeleton asa2.Skeleton

        { asa1 with Skeleton = sk1 }, { asa2 with Skeleton = sk2 }
    let addAPs (aps : list<'L>) (asa : ASA<'T, 'L>) =
        { asa with
            Skeleton = AlternatingAutomatonSkeleton.addAPsToSkeleton aps asa.Skeleton
        }

    let fixAPs (aps : list<'L>) (asa : ASA<'T, 'L>) =
        { asa with
            Skeleton = AlternatingAutomatonSkeleton.fixAPsToSkeleton aps asa.Skeleton
        }

    let projectToTargetAPs (newAPs : list<'L>) (asa : ASA<'T, 'L>) =
        { asa with
            Skeleton = AlternatingAutomatonSkeleton.projectToTargetAPs newAPs asa.Skeleton
        }

    let computeBisimulationQuotient (asa : ASA<'T, 'L>) =
        let bisimSkeleton, m =
            AutomatonSkeleton.AlternatingAutomatonSkeleton.computeBisimulationQuotient
                (fun _ -> true)
                asa.Skeleton
        {
            ASA.Skeleton = bisimSkeleton
            InitialStates = asa.InitialStates |> Set.map (Set.map (fun x -> m.[x]))
            AcceptingStates = asa.AcceptingStates |> Set.map (fun x -> m.[x])
        }
