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
module FsOmegaLib.ACA

open System
open System.IO

open SAT
open AutomatonSkeleton
open AbstractAutomaton
open NBA

exception private NotWellFormedException of string

type ACA<'T, 'L when 'T : comparison and 'L : comparison> =
    {
        Skeleton : AlternatingAutomatonSkeleton<'T, 'L>
        InitialStates : Set<Set<'T>>
        RejectingStates : Set<'T>
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

                this.RejectingStates
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

            stringWriter.WriteLine("acc-name: co-Buchi")
            stringWriter.WriteLine("Acceptance: 1 Fin (0)")


            stringWriter.WriteLine "--BODY--"

            let accCondition s =
                if this.RejectingStates.Contains s then "{0}" else ""
            stringWriter.WriteLine(
                AlternatingAutomatonSkeleton.printBodyInHanoiFormat stateStringer accCondition labelStringer this.Skeleton
            )

            stringWriter.WriteLine "--END--"

            stringWriter.ToString()


module ACA = 
    let actuallyUsedAPs (aca : ACA<'T, 'L>) =
        AlternatingAutomatonSkeleton.actuallyUsedAPs aca.Skeleton

    let convertStatesToInt (aca : ACA<'T, 'L>) =
        let idDict = aca.Skeleton.States |> Seq.mapi (fun i x -> x, i) |> Map.ofSeq

        {
            ACA.Skeleton = aca.Skeleton |> AlternatingAutomatonSkeleton.mapStates (fun x -> idDict.[x])

            InitialStates = aca.InitialStates |> Set.map (Set.map (fun x -> idDict.[x]))

            RejectingStates = aca.RejectingStates |> Set.map (fun x -> idDict.[x])
        }


    let mapAPs (f : 'L -> 'U) (aca : ACA<'T, 'L>) =
        {
            Skeleton = AlternatingAutomatonSkeleton.mapAPs f aca.Skeleton
            InitialStates = aca.InitialStates
            RejectingStates = aca.RejectingStates
        }

    let trueAutomaton () : ACA<int, 'L> =
        {
            ACA.Skeleton =
                {
                    AlternatingAutomatonSkeleton.States = set ([ 0 ])
                    APs = []
                    Edges = [ 0, [ DNF.trueDNF, Set.singleton 0 ] ] |> Map.ofList
                }
            InitialStates = Set.singleton (Set.singleton 0)
            RejectingStates = Set.empty
        }

    let falseAutomaton () : ACA<int, 'L> =
        {
            ACA.Skeleton =
                {
                    States = set ([ 0 ])
                    APs = []
                    Edges = [ 0, List.empty ] |> Map.ofList
                }
            InitialStates = Set.singleton (Set.singleton 0)
            RejectingStates = Set.singleton 0
        }

    let toHoaString (stateStringer : 'T -> string) (alphStringer : 'L -> string) (labelStringer : 'T -> string)(aca : ACA<'T, 'L>) =
        (aca :> AbstractAutomaton<'T, 'L>).ToHoaString stateStringer alphStringer labelStringer

    let findError (aca : ACA<'T, 'L>) =
        (aca :> AbstractAutomaton<'T, 'L>).FindError()

    let bringToSameAPs (autList : list<ACA<'T, 'L>>) =
        autList
        |> List.map (fun x -> x.Skeleton)
        |> AlternatingAutomatonSkeleton.bringSkeletonsToSameAps
        |> List.mapi (fun i x -> { autList.[i] with Skeleton = x })

    let bringPairToSameAPs (aca1 : ACA<'T, 'L>) (aca2 : ACA<'T, 'L>) =
        let sk1, sk2 =
            AlternatingAutomatonSkeleton.bringSkeletonPairToSameAps aca1.Skeleton aca2.Skeleton

        { aca1 with Skeleton = sk1 }, { aca2 with Skeleton = sk2 }
    let addAPs (aps : list<'L>) (aca : ACA<'T, 'L>) =
        { aca with
            Skeleton = AlternatingAutomatonSkeleton.addAPsToSkeleton aps aca.Skeleton
        }

    let fixAPs (aps : list<'L>) (aca : ACA<'T, 'L>) =
        { aca with
            Skeleton = AlternatingAutomatonSkeleton.fixAPsToSkeleton aps aca.Skeleton
        }

    let projectToTargetAPs (newAPs : list<'L>) (aca : ACA<'T, 'L>) =
        { aca with
            Skeleton = AlternatingAutomatonSkeleton.projectToTargetAPs newAPs aca.Skeleton
        }

    let computeBisimulationQuotient (aca : ACA<'T, 'L>) =
        let bisimSkeleton, m =
            AutomatonSkeleton.AlternatingAutomatonSkeleton.computeBisimulationQuotient
                (fun x -> Set.contains x aca.RejectingStates)
                aca.Skeleton
        {
            ACA.Skeleton = bisimSkeleton
            InitialStates = aca.InitialStates |> Set.map (Set.map (fun x -> m.[x]))
            RejectingStates = aca.RejectingStates |> Set.map (fun x -> m.[x])
        }
