# BB Set Viewer

A Blender extension for walking film sets like a game and framing shots without knowing Blender.
Built for the Beta Builder generation team.

- **Easy Mode**: one panel, one camera. The view is the camera: Walk (F), Fast / Preview look,
  Focal Length, Depth of Field, Focus Distance, F-Stop, Capture (picture + camera settings).
- **Artist Mode**: several cameras, locking, framing, show/hide parts of the set.
- **Walk**: mouse looks, W A S D moves, Space up, Ctrl down, Shift faster. It stops the moment you
  let go, so nothing drifts.

## Install once (Blender 4.2 or newer; 5.2 recommended)

1. **Edit → Preferences → Get Extensions**. If asked, click **Allow Online Access**.
2. Open the **Repositories** dropdown (top right) → **+** → **Add Remote Repository**.
3. URL: `https://raw.githubusercontent.com/Lakao456/bb-set-viewer/main/repo/index.json`
   Tick **Check for Updates on Startup**, then **Create**.
4. Search **BB Set Viewer** → **Install**.

Had the old single-file version (`bb_set_viewer.py`)? Remove it first: **Add-ons** → BB Set Viewer →
**⌄** → **Uninstall**.

## Updates

Blender checks on startup. When a new version is out, **Get Extensions** shows **Update**: one click.
Or: Get Extensions → Repositories dropdown → **Check for Updates**.

## Opening a set

Set files open straight into their mode. A set file also carries a copy of the tools for people
without the extension; the installed extension always takes priority.

## Publishing (maintainer)

Bump `version` in the add-on's `bl_info`, then run `publish_bb_set_viewer.py` from the Beta
Builder toolchain. It builds the package into `repo/`, regenerates `repo/index.json`, commits
and pushes.
