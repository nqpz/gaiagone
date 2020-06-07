import "lib/github.com/diku-dk/lys/lys"
import "lib/github.com/diku-dk/cpprandom/random"
import "lib/github.com/athas/vector/vspace"

module vec2 = mk_vspace_2d f32
module rnge = minstd_rand
module dist = uniform_real_distribution f32 rnge
type rng = rnge.rng

let n_planets = 10i32

let granularity = 50i32

let max_spike_diff_factor = 2.0f32

type point = vec2.vector

type particle = {p: point, pd: point, color: argb.colour}

type spike = {size: f32, color: argb.colour}

type planet = {center: point,
               spikes: [granularity]spike}

type collision_info = {has_collision: bool,
                       spike0: (i32, f32), spike1: (i32, f32)}

type debug_info = {factor: f32,
                   factor_lower: f32,
                   factor_upper: f32,
                   n_iters: i32,
                   newly_consumed_mass: f32,
                   planet_mass_theoretical: f32,
                   spike_diff_factor: f32}

let debug_init: debug_info =
  {factor= -1,
   factor_lower= -1,
   factor_upper= -1,
   n_iters= -1,
   newly_consumed_mass=0,
   planet_mass_theoretical= -1,
   spike_diff_factor=0}

let point_sum: []point -> point = reduce_comm (vec2.+) {y=0, x=0}

let check_collision (pl: planet) (po: point): collision_info =
  let yrel = po.y - pl.center.y
  let xrel = po.x - pl.center.x
  let dist = f32.sqrt (yrel**2 + xrel**2)
  let degrees = f32.atan2 yrel xrel
  let spike_idx_base = r32 granularity * ((degrees + f32.pi) / (2 * f32.pi))
  let spike_idx0 = t32 spike_idx_base % granularity
  let spike_idx1 = (spike_idx0 + 1) % granularity
  let spike_idx_favor1 = spike_idx_base % 1
  let spike_idx_favor0 = 1 - spike_idx_favor1
  let spike = pl.spikes[spike_idx0].size * spike_idx_favor0 +
              pl.spikes[spike_idx1].size * spike_idx_favor1
  let has_collision = dist <= spike
  in {has_collision, spike0=(spike_idx0, spike_idx_favor0), spike1=(spike_idx1, spike_idx_favor1)}

let particle_mass = 0.00005f32

let planet_mass' (spike_sizes: []f32): f32 =
  let segments = map (\i -> (i, (i + 1) % granularity)) (0..<length spike_sizes)
  let segment_mass ((i, j): (i32, i32)): f32 =
    let size0 = spike_sizes[i]
    let size1 = spike_sizes[j]
    -- Integrate (size0 i + size1 - i size1)**2 * f32.pi / r32 granularity  for [0..1]:
    let size_integrated i = f32.pi * (i * size0 + size1 - size1 * i)**3 / (r32 granularity * (3 * size0 - 3 * size1))
    in if size0 != size1
       then size_integrated 1 - size_integrated 0
       else size0**2 * f32.pi / r32 granularity
  in f32.sum (map segment_mass segments)

let planet_mass (pl: planet): f32 = planet_mass' (map (.size) pl.spikes)

let binary_search (goal: f32) (delta_goal: f32) (lower_init: f32) (upper_init: f32)
                  (max_iter: i32) (f: f32 -> f32): (f32, i32) =
  let pick (lower: f32) (upper: f32): f32 = lower + (upper - lower) / 2
  let inp_init = pick lower_init upper_init
  let (inp, _, _, _, n_iters) =
    loop (inp, res, lower, upper, i) = (inp_init, f inp_init, lower_init, upper_init, 0)
    while f32.abs (res - goal) > delta_goal && i < max_iter
    do let (inp', lower', upper') =
         if res > goal
         then (pick lower inp, lower, inp)
         else (pick inp upper, inp, upper)
       in (inp', f inp', lower', upper', i + 1)
  in (inp, n_iters)

type text_content = (i32, f32, f32, f32, i32, f32, f32, f32, f32, i32, f32, f32, f32)
module lys: lys with text_content = text_content = {
  type~ state = {planets: [n_planets]planet,
                 particles: []particle,
                 mouse: {y: i32, x: i32},
                 view_zoom: f32, view_center: point,
                 rng: rng,
                 h: i32, w: i32,
                 debugs: [n_planets]debug_info}

  let grab_mouse = false

  let gen_planet (rng: rng): (rng, planet) =
    let rngs = rnge.split_rng granularity rng
    let (rngs, spikes) = unzip (map (\rng ->
                                       let (rng, size) = dist.rand (0.05, 0.06) rng
                                       let (rng, r) = dist.rand (0.2, 0.8) rng
                                       let (rng, g) = dist.rand (0.2, 0.8) rng
                                       let (rng, b) = dist.rand (0.2, 0.8) rng
                                       let color = argb.from_rgba r g b 1.0
                                       in (rng, {size, color})) rngs)
    let rng = rnge.join_rng rngs
    let (rng, ycenter) = dist.rand (-4.5, 4.5) rng
    let (rng, xcenter) = dist.rand (-4.5, 4.5) rng
    in (rng, {center={y=ycenter, x=xcenter}, spikes})

  let gen_planets (rng: rng): (rng, []planet) =
    let rngs = rnge.split_rng n_planets rng
    let (rngs, planets) = unzip (map gen_planet rngs)
    let rng = rnge.join_rng rngs
    in (rng, planets)

  let gen_particles (rng: rng): (rng, []particle) =
    let rngs = rnge.split_rng 100000 rng
    let (rngs, ys) = unzip (map (dist.rand (-4.5, 4.5)) rngs)
    let (rngs, xs) = unzip (map (dist.rand (-4.5, 4.5)) rngs)
    let (rngs, yds) = unzip (map (dist.rand (-0.005, 0.005)) rngs)
    let (rngs, xds) = unzip (map (dist.rand (-0.005, 0.005)) rngs)
    let (rngs, rs) = unzip (map (dist.rand (0.2, 0.8)) rngs)
    let (rngs, gs) = unzip (map (dist.rand (0.2, 0.8)) rngs)
    let (rngs, bs) = unzip (map (dist.rand (0.2, 0.8)) rngs)
    let colors = map3 (\r g b -> argb.from_rgba r g b 1.0) rs gs bs
    let rng = rnge.join_rng rngs
    let ps = map5 (\y x yd xd color -> {p={y, x}, pd={y=yd, x=xd}, color}) ys xs yds xds colors
    in (rng, ps)

  let init (seed: u32) (h: i32) (w: i32): state =
    let rng = rnge.rng_from_seed [i32.u32 seed]
    let (rng, planets) = gen_planets rng
    let (rng, particles) = gen_particles rng
    in {planets, particles,
        mouse={y=0, x=0},
        view_zoom=0.1, view_center={y=0, x=0},
        rng, h, w,
        debugs=replicate n_planets debug_init}

  let accel (center: point) (mass: f32) (p: point): point =
    if p == center
    then {y=0, x=0}
    else let r = vec2.(center - p)
         let rsqr = vec2.dot r r
         let invr = 1 / f32.sqrt rsqr
         let invr2 = invr * invr
         let s = mass * invr2
         in vec2.scale s r

  let color_merge ((color0, factor0): (argb.colour, f32)) ((color1, factor1): (argb.colour, f32)): argb.colour =
    if color0 == 0
    then color1
    else if color1 == 0
    then color0
    else argb.mix factor0 color0 factor1 color1

  let step (td: f32) (s: state): state =
    let particles = map (\{p, pd, color} ->
                           let pdd = point_sum (map (\pl -> accel pl.center (planet_mass pl) p) s.planets)
                                     vec2.+ point_sum (map (\part -> accel part.p particle_mass p) s.particles)
                           in {p=vec2.(p + scale td pd), pd=vec2.(pd + scale td pdd), color}) s.particles
    -- Assume planets don't overlap.

    let step_planet (pl: planet) (debug_old: debug_info): (planet, debug_info) =
      let collisions = map (check_collision pl <-< (.p)) particles
      let (particles_collisions, _particles_unchanged) = partition ((.has_collision) <-< (.1)) (zip particles collisions)
      in if length particles_collisions == 0
         then (pl, debug_old)
         else let collisions' = map (.1) particles_collisions
              let spike_merge spike0 spike1 =
                {size=spike0.size + spike1.size, color=color_merge (spike0.color, spike0.size) (spike1.color, spike1.size)}
              let spike_empty = {size=0, color=0} -- ignore black, use as special value
              let spikes_empty = map (const spike_empty) pl.spikes
              let n = length collisions' * 2
              let indices = map (.spike0.0) collisions' ++ map (.spike1.0) collisions' :> [n]i32
              let values = map (\pc -> {size=particle_mass * pc.1.spike0.1, color=pc.0.color}) particles_collisions ++
                               map (\pc -> {size=particle_mass * pc.1.spike1.1, color=pc.0.color}) particles_collisions :> [n]spike
              let spikes_additions = reduce_by_index spikes_empty spike_merge spike_empty indices values
              let new_mass = particle_mass * r32 (length particles_collisions)
              let planet_mass_goal = planet_mass pl + new_mass
              let calc_spikes (factor: f32): []spike = map2 (\s sa ->
                                                               let sa_size' = factor * sa.size
                                                               in {size=s.size + sa_size',
                                                                   color=color_merge (s.color, s.size) (sa.color, sa_size')})
                                                            pl.spikes spikes_additions
              let calc_mass (factor: f32): f32 = planet_mass' (map (.size) (calc_spikes factor))
              let (factor_lower, factor_upper) = -- finetune maybe
                (0, f32.sqrt (planet_mass_goal / f32.pi) / f32.maximum (map (.size) spikes_additions))

              let binsearch_goal_delta = 0.00001
              let max_iter = 100
              let (factor_approx, n_iters) = binary_search planet_mass_goal binsearch_goal_delta factor_lower factor_upper max_iter calc_mass
              let spikes' = calc_spikes factor_approx

              let spike_min = f32.minimum (map (.size) spikes')
              let spike_diff_factor = f32.maximum (map (.size) spikes') / spike_min
              let (spikes'', factor_approx, n_iters) =
                if spike_diff_factor <= max_spike_diff_factor
                then (spikes', factor_approx, n_iters)
                else let spikes_reshaped =
                       map (\(s: spike) ->
                              s with size = if s.size / spike_min <= max_spike_diff_factor
                                            then s.size
                                            else spike_min * max_spike_diff_factor) spikes'
                     let calc_spikes' (factor: f32): []spike =
                       map (\(s: spike) -> s with size = factor * s.size) spikes_reshaped
                     let calc_mass' (factor: f32): f32 = planet_mass' (map (.size) (calc_spikes' factor))
                     let (factor_lower', factor_upper') = (1, spike_diff_factor)
                     let (factor_reshape_approx, n_iters) =
                       binary_search planet_mass_goal binsearch_goal_delta factor_lower' factor_upper' max_iter calc_mass'
                     in (calc_spikes' factor_reshape_approx, factor_reshape_approx, n_iters)

              let debug = {factor=factor_approx,
                           factor_lower=factor_lower,
                           factor_upper=factor_upper,
                           n_iters=n_iters,
                           newly_consumed_mass=new_mass,
                           planet_mass_theoretical=planet_mass_goal,
                           spike_diff_factor}
              in (pl with spikes = spikes'', debug)

    let (planets', debugs) = unzip (map2 step_planet s.planets s.debugs)

    -- risk of tunneling effect, but we don't care
    let collisions = map (\part -> any (\pl -> (check_collision pl part.p).has_collision) s.planets) particles
    let (_particles_collisions, particles_unchanged) = partition (.1) (zip particles collisions)
    let particles' = map (.0) particles_unchanged
    in s with planets = planets'
         with particles = particles'
         with debugs = debugs

  let resize (h: i32) (w: i32) (s: state): state =
    s with h = h with w = w

  let xy_factor (s: state): f32 =
    r32 (i32.min s.h s.w) * s.view_zoom

  let zoom_at_mouse (zoom_factor: f32) (s: state): state =
    let xb = r32 (s.mouse.x - s.w / 2)
    let xd = xb / xy_factor s - xb / (xy_factor s * zoom_factor)
    let yb = r32 (s.mouse.y - s.h / 2)
    let yd = yb / xy_factor s - yb / (xy_factor s * zoom_factor)
    in s with view_zoom = s.view_zoom * zoom_factor
         with view_center.y = s.view_center.y + yd
         with view_center.x = s.view_center.x + xd

  let event (e: event) (s: state): state =
    match e
    case #step td ->
      step td s
    case #keydown {key} ->
      if key == SDLK_r
      then let (rng, planets) = gen_planets s.rng
           let (rng, particles) = gen_particles rng
           in s with planets = planets
                with particles = particles
                with rng = rng
      -- else if key == SDLK_SPACE
      -- then step 0.01 s
      else s
    case #mouse {buttons, x, y} ->
      let s = if bool.i32 (buttons & 0b001)
              then let y_diff = s.mouse.y - y
                   let x_diff = s.mouse.x - x
                   in s with view_center.y = s.view_center.y + r32 y_diff / xy_factor s
                        with view_center.x = s.view_center.x + r32 x_diff / xy_factor s
              else s
      let s = s with mouse = {y, x}
      in s

    case #wheel {dx=_, dy} ->
      let zoom_factor = 1 + r32 dy * 0.02
      in zoom_at_mouse zoom_factor s
    case _ -> s

  let render (s: state): [][]argb.colour =
    let render_planet_at (yi: i32) (xi: i32): argb.colour =
      let y = r32 (yi - s.h / 2) / xy_factor s + s.view_center.y
      let x = r32 (xi - s.w / 2) / xy_factor s + s.view_center.x
      let planet_colors = map (\pl -> let c = check_collision pl {y, x}
                                      in if c.has_collision
                                         then let color0 = pl.spikes[c.spike0.0].color
                                              let color1 = pl.spikes[c.spike1.0].color
                                              in argb.mix c.spike0.1 color0 c.spike1.1 color1
                                         else 0) s.planets
      in (reduce_comm (\(c0, m0) (c1, m1) -> (color_merge (c0, m0) (c1, m1), m0 + m1)) (0, 0) (zip planet_colors (map planet_mass s.planets))).0

    let particle_index ({p={y, x}, pd=_, color}: particle): (i32, argb.colour) =
      let xy_fac = r32 (i32.min s.h s.w)
      let x_offset_base = r32 (i32.max 0 (s.w - s.h)) / xy_fac
      let y_offset_base = r32 (i32.max 0 (s.h - s.w)) / xy_fac
      let x_offset = (x_offset_base / 2)
      let y_offset = (y_offset_base / 2)

      let y = t32 (xy_fac * ((y * s.view_zoom + 0.5 + y_offset) - s.view_center.y * s.view_zoom))
      let x = t32 (xy_fac * ((x * s.view_zoom + 0.5 + x_offset) - s.view_center.x * s.view_zoom))
      in if y >= 0 && y < s.h && x >= 0 && x < s.w
         then (y * s.w + x, color)
         else (-1, 0)

    let pixels = flatten (tabulate_2d s.h s.w render_planet_at)
    let (points_indices, points_values) = unzip (map particle_index s.particles)
    let pixels = scatter pixels points_indices points_values
    in unflatten s.h s.w pixels

  type text_content = text_content

  let text_format () = "FPS: %d\nPlanet 0 mass: %f\nParticle 0 pos (%f, %f)\nParticles: %d\nCollective particle mass: %f\n\nFactor: %f (lower: %f, upper: %f)\nBinary search iterations: %d\nNewly consumed mass: %f\nTheoretical current planet 0 mass: %f\nSpike diff factor: %f"

  let text_content (fps: f32) (s: state): text_content =
    (t32 fps, planet_mass s.planets[0], if length s.particles > 0 then s.particles[0].p.y else -1, if length s.particles > 0 then s.particles[0].p.x else -1, length s.particles, particle_mass * r32 (length s.particles), s.debugs[0].factor, s.debugs[0].factor_lower, s.debugs[0].factor_upper, s.debugs[0].n_iters, s.debugs[0].newly_consumed_mass, s.debugs[0].planet_mass_theoretical, s.debugs[0].spike_diff_factor)

  let text_colour = const argb.white
}
