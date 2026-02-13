import math
import os
import tempfile
import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog
from tkinter import ttk

import cv2
import matplotlib.pyplot as plt
import numpy as np
from fpdf import FPDF
from PIL import Image, ImageTk

# ==============================
# Customizable drawing colors
# ==============================
BOUNDARY_POINT_COLOR = "#1e90ff"
BOUNDARY_LINE_COLOR = "#00b894"
BARCHART_BOUNDARY_POINT_COLOR = "#7c3aed"
BARCHART_BOUNDARY_LINE_COLOR = "#a855f7"
CENTER_COLOR = "#e63946"
ZONE_LINE_COLOR = "#f4a261"
ZONE_TEXT_COLOR = "#264653"
CARDINAL_LINE_COLOR = "#6a4c93"
CARDINAL_TEXT_COLOR = "#2d1e2f"

CANVAS_BG = "#f2f2f2"
IMAGE_CANVAS_PADDING = 28  # Extra workspace around image inside canvas.

# Modern UI palette
APP_BG = "#eef2f7"
CARD_BG = "#f8fafc"
TEXT_PRIMARY = "#0f172a"
TEXT_SECONDARY = "#334155"
ACCENT = "#2563eb"
ACCENT_LIGHT = "#dbeafe"


class PlotAnalyzerApp:
    """Desktop app for plotting boundary, center, directional zones, and area calculations."""

    ZONE_NAMES = [
        "N", "NNE", "NE", "ENE",
        "E", "ESE", "SE", "SSE",
        "S", "SSW", "SW", "WSW",
        "W", "WNW", "NW", "NNW",
    ]

    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("Vastu Plot Studio")
        self.root.geometry("1200x760")

        # Original image (OpenCV BGR) and canvas display state.
        self.original_bgr = None
        self.display_photo = None  # Keep reference to prevent garbage collection.

        # Image placement/scaling metadata for coordinate conversion.
        self.display_scale = 1.0
        self.image_offset_x = 0
        self.image_offset_y = 0
        self.display_w = 0
        self.display_h = 0
        self.base_image_item = None
        self.last_render_key = None
        self.overlay_redraw_job = None

        # Geometry data in original image coordinates.
        self.boundary_points = []  # Boundary used for center / directions workflow.
        self.barchart_boundary_points = []  # Separate boundary used for bar-chart area calculations.
        self.polygon_closed = False
        self.barchart_polygon_closed = False
        self.center_point = None
        self.north_tilt_deg = 0.0
        self.zones_drawn = False
        self.cursor_img_point = None
        self.boundary_mode = tk.StringVar(value="manual")
        self.zone_areas_cache = None
        self.cardinal_drawn = False
        self.progress_win = None
        self.progress_label_var = tk.StringVar(value="")
        self.progress_value_var = tk.DoubleVar(value=0.0)
        self.active_boundary_target = tk.StringVar(value="center")

        self._configure_styles()
        self._build_ui()

    def _configure_styles(self):
        """Define modern ttk styles used by the app."""
        style = ttk.Style(self.root)
        style.theme_use("clam")

        style.configure("App.TFrame", background=APP_BG)
        style.configure("Card.TFrame", background=CARD_BG, relief="flat")
        style.configure("Header.TFrame", background="#0b1220")
        style.configure("HeaderTitle.TLabel", background="#0b1220", foreground="#f8fafc", font=("Helvetica", 16, "bold"))
        style.configure("HeaderMeta.TLabel", background="#0b1220", foreground="#93c5fd", font=("Helvetica", 10))
        style.configure("WorkspaceTitle.TLabel", background=CARD_BG, foreground=TEXT_PRIMARY, font=("Helvetica", 11, "bold"))
        style.configure("CardTitle.TLabel", background=CARD_BG, foreground=TEXT_PRIMARY, font=("Helvetica", 15, "bold"))
        style.configure("Section.TLabel", background=CARD_BG, foreground=TEXT_SECONDARY, font=("Helvetica", 10, "bold"))
        style.configure("Meta.TLabel", background=CARD_BG, foreground="#64748b", font=("Helvetica", 9))
        style.configure("Status.TLabel", background="#e2e8f0", foreground="#0f172a", font=("Helvetica", 9))
        style.configure("Badge.TLabel", background="#1d4ed8", foreground="#ffffff", font=("Helvetica", 9, "bold"))

        style.configure(
            "Primary.TButton",
            background=ACCENT,
            foreground="#ffffff",
            font=("Helvetica", 10, "bold"),
            borderwidth=0,
            focusthickness=0,
            padding=(10, 7),
        )
        style.map("Primary.TButton", background=[("active", "#1d4ed8"), ("pressed", "#1e40af")])

        style.configure(
            "Action.TButton",
            background="#ffffff",
            foreground=TEXT_PRIMARY,
            font=("Helvetica", 10),
            bordercolor="#cbd5e1",
            lightcolor="#ffffff",
            darkcolor="#ffffff",
            padding=(10, 7),
        )
        style.map("Action.TButton", background=[("active", "#eff6ff"), ("pressed", "#dbeafe")])

        style.configure("Card.TRadiobutton", background=CARD_BG, foreground=TEXT_PRIMARY, font=("Helvetica", 10))
        style.map("Card.TRadiobutton", background=[("active", CARD_BG)])
        # Slim scrollbar style for a cleaner modern look.
        style.configure(
            "Slim.Vertical.TScrollbar",
            gripcount=0,
            background="#cbd5e1",
            darkcolor="#cbd5e1",
            lightcolor="#cbd5e1",
            troughcolor=CARD_BG,
            bordercolor=CARD_BG,
            arrowcolor=CARD_BG,
            arrowsize=8,
            width=8,
        )

    # ------------------------------
    # UI setup
    # ------------------------------
    def _build_ui(self):
        """Create main layout: left canvas and right control panel."""
        self.root.configure(bg=APP_BG)
        self.root.columnconfigure(0, weight=1)
        self.root.columnconfigure(1, weight=0)
        self.root.rowconfigure(0, weight=1)

        app_frame = ttk.Frame(self.root, style="App.TFrame", padding=12)
        app_frame.grid(row=0, column=0, columnspan=2, sticky="nsew")
        app_frame.columnconfigure(0, weight=1)
        app_frame.columnconfigure(1, weight=0)
        app_frame.rowconfigure(1, weight=1)

        # Top header bar.
        header = ttk.Frame(app_frame, style="Header.TFrame", padding=(14, 10))
        header.grid(row=0, column=0, columnspan=2, sticky="ew", pady=(0, 10))
        header.columnconfigure(0, weight=1)
        ttk.Label(header, text="Vastu Plot Studio", style="HeaderTitle.TLabel").grid(row=0, column=0, sticky="w")
        ttk.Label(
            header,
            text="Image • Geometry • Zones • PDF Reports",
            style="HeaderMeta.TLabel",
        ).grid(row=1, column=0, sticky="w", pady=(2, 0))
        ttk.Label(header, text="DESKTOP TOOL", style="Badge.TLabel", padding=(8, 4)).grid(
            row=0, column=1, rowspan=2, sticky="e"
        )

        # Left: drawing canvas
        canvas_frame = tk.Frame(app_frame, bg=CANVAS_BG, bd=1, relief="solid", highlightthickness=0)
        canvas_frame.grid(row=1, column=0, sticky="nsew", padx=(0, 10))
        canvas_frame.rowconfigure(1, weight=1)
        canvas_frame.columnconfigure(0, weight=1)

        canvas_title = ttk.Frame(canvas_frame, style="Card.TFrame", padding=(8, 6))
        canvas_title.grid(row=0, column=0, sticky="ew")
        ttk.Label(canvas_title, text="Plot Workspace", style="WorkspaceTitle.TLabel").pack(side="left")
        ttk.Label(
            canvas_title,
            text="Click to mark boundary and geometry overlays",
            style="Meta.TLabel",
        ).pack(side="right")

        self.canvas = tk.Canvas(canvas_frame, bg=CANVAS_BG, highlightthickness=0)
        self.canvas.grid(row=1, column=0, sticky="nsew")
        self.canvas.bind("<Button-1>", self._on_canvas_click)
        self.canvas.bind("<Motion>", self._on_canvas_motion)
        self.canvas.bind("<Leave>", self._on_canvas_leave)
        self.canvas.bind("<Configure>", self._on_canvas_resize)

        # Right: scrollable controls panel
        controls_host = ttk.Frame(app_frame, width=300, style="Card.TFrame")
        controls_host.grid(row=1, column=1, sticky="ns")
        controls_host.grid_propagate(False)
        controls_host.rowconfigure(0, weight=1)
        controls_host.columnconfigure(0, weight=1)

        controls_canvas = tk.Canvas(
            controls_host,
            bg=CARD_BG,
            highlightthickness=0,
            bd=0,
            width=300,
        )
        controls_canvas.grid(row=0, column=0, sticky="nsew")

        controls_scroll = ttk.Scrollbar(
            controls_host,
            orient="vertical",
            command=controls_canvas.yview,
            style="Slim.Vertical.TScrollbar",
        )
        controls_scroll.grid(row=0, column=1, sticky="ns")
        controls_canvas.configure(yscrollcommand=controls_scroll.set)

        controls = ttk.Frame(controls_canvas, style="Card.TFrame", padding=14)
        controls_window = controls_canvas.create_window((0, 0), window=controls, anchor="nw")

        def _on_controls_frame_configure(_event):
            controls_canvas.configure(scrollregion=controls_canvas.bbox("all"))

        def _on_controls_canvas_configure(event):
            controls_canvas.itemconfig(controls_window, width=event.width)

        def _pointer_inside_controls(event):
            """Return True when current pointer location is inside controls panel."""
            widget = controls_canvas.winfo_containing(event.x_root, event.y_root)
            while widget is not None:
                if widget == controls_canvas:
                    return True
                widget = getattr(widget, "master", None)
            return False

        def _smooth_scroll_pixels(delta_pixels):
            """Smoothly scroll canvas by pixel distance using yview_moveto."""
            bbox = controls_canvas.bbox("all")
            if not bbox:
                return
            content_h = max(1, bbox[3] - bbox[1])
            viewport_h = max(1, controls_canvas.winfo_height())
            scrollable_h = max(1, content_h - viewport_h)

            current_first = controls_canvas.yview()[0]
            current_px = current_first * scrollable_h
            target_px = max(0.0, min(float(scrollable_h), current_px + float(delta_pixels)))
            controls_canvas.yview_moveto(target_px / float(scrollable_h))

        def _on_controls_mousewheel(event):
            # Scroll only when pointer is over controls panel.
            if not _pointer_inside_controls(event):
                return

            if getattr(event, "num", None) == 4:
                _smooth_scroll_pixels(-56)
                return
            if getattr(event, "num", None) == 5:
                _smooth_scroll_pixels(56)
                return

            delta = getattr(event, "delta", 0)
            if delta == 0:
                return

            # Trackpad-friendly: convert wheel/gesture delta to pixel movement.
            if abs(delta) >= 120:
                scroll_px = (-delta / 120.0) * 56.0
            else:
                # Smooth small deltas (common on macOS trackpads).
                scroll_px = -delta * 2.8
            _smooth_scroll_pixels(scroll_px)

        controls.bind("<Configure>", _on_controls_frame_configure)
        controls_canvas.bind("<Configure>", _on_controls_canvas_configure)
        controls_canvas.bind("<Enter>", lambda _e: controls_canvas.focus_set())
        controls_canvas.bind_all("<MouseWheel>", _on_controls_mousewheel)
        controls_canvas.bind_all("<Button-4>", _on_controls_mousewheel)
        controls_canvas.bind_all("<Button-5>", _on_controls_mousewheel)

        ttk.Label(
            controls,
            text="Controls",
            style="CardTitle.TLabel",
            anchor="w"
        ).pack(fill="x", pady=(0, 10))
        ttk.Label(controls, text="Plot workflow and export actions", style="Meta.TLabel", anchor="w").pack(
            fill="x", pady=(0, 10)
        )

        ttk.Label(
            controls, text="Boundary Detection", anchor="w", style="Section.TLabel"
        ).pack(fill="x", pady=(2, 2))
        ttk.Button(
            controls,
            text="Boundary for Center",
            command=self.set_center_boundary_target,
            style="Action.TButton",
        ).pack(fill="x", pady=(2, 3))
        ttk.Button(
            controls,
            text="Boundary for Barchart",
            command=self.set_barchart_boundary_target,
            style="Action.TButton",
        ).pack(fill="x", pady=(0, 6))
        ttk.Radiobutton(
            controls,
            text="Manual",
            value="manual",
            variable=self.boundary_mode,
            command=self._on_boundary_mode_change,
            style="Card.TRadiobutton",
        ).pack(fill="x")
        ttk.Radiobutton(
            controls,
            text="Automated",
            value="auto",
            variable=self.boundary_mode,
            command=self._on_boundary_mode_change,
            style="Card.TRadiobutton",
        ).pack(fill="x")
        ttk.Button(
            controls,
            text="Auto Detect Boundary",
            command=self.auto_detect_boundary,
            style="Primary.TButton",
        ).pack(
            fill="x", pady=(8, 10)
        )

        ttk.Separator(controls, orient="horizontal").pack(fill="x", pady=(2, 8))
        ttk.Label(controls, text="Geometry", style="Section.TLabel", anchor="w").pack(fill="x", pady=(0, 4))
        geometry_buttons = [
            ("Upload Image", self.upload_image),
            ("Mark Center", self.mark_center),
            ("Set North Tilt", self.set_north_tilt),
            ("Mark N/S/E/W", self.mark_cardinal_lines),
            ("Mark 16 Zones", self.mark_16_zones),
            ("Mark Devta", self.mark_devta),
        ]

        for txt, cmd in geometry_buttons:
            ttk.Button(
                controls,
                text=txt,
                command=cmd,
                style="Action.TButton",
            ).pack(fill="x", pady=3)

        ttk.Separator(controls, orient="horizontal").pack(fill="x", pady=(8, 8))
        ttk.Label(controls, text="Calculations", style="Section.TLabel", anchor="w").pack(fill="x", pady=(0, 4))
        calc_buttons = [
            ("Calculate Plot Area", self.calculate_plot_area),
            ("Calculate Zone Areas", self.calculate_zone_areas),
            ("Clear Markings", self.clear_markings),
        ]
        for txt, cmd in calc_buttons:
            ttk.Button(
                controls,
                text=txt,
                command=cmd,
                style="Action.TButton",
            ).pack(fill="x", pady=3)

        ttk.Separator(controls, orient="horizontal").pack(fill="x", pady=(8, 8))
        ttk.Label(controls, text="Reports", style="Section.TLabel", anchor="w").pack(fill="x", pady=(0, 4))
        ttk.Button(
            controls,
            text="Export PDF",
            command=self.export_pdf_report,
            style="Primary.TButton",
        ).pack(fill="x", pady=3)
        ttk.Button(
            controls,
            text="Remove Image",
            command=self.remove_image,
            style="Action.TButton",
        ).pack(fill="x", pady=(6, 3))

        self.status_var = tk.StringVar(value="Load an image to begin.")
        ttk.Label(
            controls,
            textvariable=self.status_var,
            wraplength=230,
            justify="left",
            style="Status.TLabel",
            padding=8,
        ).pack(fill="x", pady=(12, 0))

    # ------------------------------
    # Image loading and display
    # ------------------------------
    def upload_image(self):
        """Load JPG/PNG image and reset all geometry state."""
        file_path = filedialog.askopenfilename(
            title="Select Plot Image",
            filetypes=[("Image files", "*.jpg *.jpeg *.png")],
        )
        if not file_path:
            return

        bgr = cv2.imread(file_path)
        if bgr is None:
            messagebox.showerror("Error", "Failed to load image. Please select a valid JPG/PNG.")
            return

        # Offer cropping right after upload before any further processing.
        if messagebox.askyesno("Crop Image", "Do you want to crop the uploaded image before proceeding?"):
            crop_applied, cropped_bgr = self._open_crop_dialog(bgr)
            if crop_applied and cropped_bgr is not None:
                bgr = cropped_bgr

        self.original_bgr = bgr
        self.clear_geometry_only()
        self._render_canvas()
        self.status_var.set(
            "Image loaded. Choose Manual or Automated boundary detection from controls."
        )

    def _open_crop_dialog(self, bgr_image):
        """
        Open an interactive crop dialog.
        User draws a rectangle and clicks 'Apply Crop' to confirm.
        Returns: (crop_applied: bool, cropped_bgr: np.ndarray | None)
        """
        img_h, img_w = bgr_image.shape[:2]
        max_preview_w = 960
        max_preview_h = 700
        preview_scale = min(max_preview_w / img_w, max_preview_h / img_h, 1.0)
        preview_w = max(1, int(img_w * preview_scale))
        preview_h = max(1, int(img_h * preview_scale))

        rgb = cv2.cvtColor(bgr_image, cv2.COLOR_BGR2RGB)
        preview_pil = Image.fromarray(rgb).resize((preview_w, preview_h), Image.LANCZOS)
        preview_photo = ImageTk.PhotoImage(preview_pil)

        crop_win = tk.Toplevel(self.root)
        crop_win.title("Crop Image")
        crop_win.transient(self.root)
        crop_win.grab_set()
        crop_win.resizable(False, False)

        tk.Label(
            crop_win,
            text="Drag to select crop area, then click 'Apply Crop'.",
            font=("Helvetica", 10),
        ).pack(fill="x", padx=10, pady=(10, 6))

        canvas = tk.Canvas(crop_win, width=preview_w, height=preview_h, bg="#111111", highlightthickness=0)
        canvas.pack(padx=10, pady=(0, 10))
        canvas.create_image(0, 0, image=preview_photo, anchor="nw")
        # Keep local reference to avoid Tkinter image garbage collection.
        canvas.image_ref = preview_photo

        button_row = tk.Frame(crop_win)
        button_row.pack(fill="x", padx=10, pady=(0, 10))

        selection = {"x0": None, "y0": None, "x1": None, "y1": None, "rect_id": None}
        result = {"applied": False, "cropped": None}

        def _clamp_canvas_point(x, y):
            return (max(0, min(preview_w, x)), max(0, min(preview_h, y)))

        def _on_press(event):
            x, y = _clamp_canvas_point(event.x, event.y)
            selection["x0"], selection["y0"] = x, y
            selection["x1"], selection["y1"] = x, y
            if selection["rect_id"] is not None:
                canvas.delete(selection["rect_id"])
            selection["rect_id"] = canvas.create_rectangle(
                x, y, x, y, outline="#f59e0b", width=2, dash=(5, 3)
            )

        def _on_drag(event):
            if selection["x0"] is None:
                return
            x, y = _clamp_canvas_point(event.x, event.y)
            selection["x1"], selection["y1"] = x, y
            canvas.coords(selection["rect_id"], selection["x0"], selection["y0"], x, y)

        def _apply_crop():
            if selection["x0"] is None or selection["x1"] is None:
                messagebox.showwarning("Crop", "Please draw a crop rectangle first.", parent=crop_win)
                return

            x0, x1 = sorted([selection["x0"], selection["x1"]])
            y0, y1 = sorted([selection["y0"], selection["y1"]])
            if (x1 - x0) < 5 or (y1 - y0) < 5:
                messagebox.showwarning("Crop", "Selected crop area is too small.", parent=crop_win)
                return

            # Convert preview coordinates back to original image coordinates.
            ox0 = max(0, min(img_w - 1, int(round(x0 / preview_scale))))
            oy0 = max(0, min(img_h - 1, int(round(y0 / preview_scale))))
            ox1 = max(1, min(img_w, int(round(x1 / preview_scale))))
            oy1 = max(1, min(img_h, int(round(y1 / preview_scale))))

            if ox1 <= ox0 or oy1 <= oy0:
                messagebox.showwarning("Crop", "Invalid crop selection.", parent=crop_win)
                return

            result["cropped"] = bgr_image[oy0:oy1, ox0:ox1].copy()
            result["applied"] = True
            crop_win.destroy()

        def _skip_crop():
            crop_win.destroy()

        ttk.Button(button_row, text="Apply Crop", command=_apply_crop, style="Primary.TButton").pack(side="left")
        ttk.Button(button_row, text="Skip", command=_skip_crop, style="Action.TButton").pack(side="left", padx=(8, 0))

        canvas.bind("<ButtonPress-1>", _on_press)
        canvas.bind("<B1-Motion>", _on_drag)
        crop_win.protocol("WM_DELETE_WINDOW", _skip_crop)

        crop_win.wait_window()
        return result["applied"], result["cropped"]

    def _on_canvas_resize(self, _event):
        """Re-render image and overlays when canvas size changes."""
        if self.original_bgr is not None:
            self._render_canvas()

    def _on_boundary_mode_change(self):
        """Update status when user switches between manual and automated boundary modes."""
        mode_name = "Manual" if self.boundary_mode.get() == "manual" else "Automated"
        target = "Center" if self.active_boundary_target.get() == "center" else "Barchart"
        self.status_var.set(f"{mode_name} boundary mode selected for {target}.")
        self.cursor_img_point = None
        self._render_canvas()

    def set_center_boundary_target(self):
        """Set point marking target to center boundary."""
        self.active_boundary_target.set("center")
        self.cursor_img_point = None
        self.status_var.set("Now marking boundary for Center workflow.")
        self._render_canvas()

    def set_barchart_boundary_target(self):
        """Set point marking target to barchart boundary area."""
        self.active_boundary_target.set("barchart")
        self.cursor_img_point = None
        self.status_var.set("Now marking boundary for Barchart area workflow.")
        self._render_canvas()

    def _render_canvas(self):
        """Draw scaled image (cached) and overlays."""
        if self.original_bgr is None:
            self.canvas.delete("all")
            self.base_image_item = None
            self.last_render_key = None
            return

        canvas_w = max(self.canvas.winfo_width(), 1)
        canvas_h = max(self.canvas.winfo_height(), 1)
        img_h, img_w = self.original_bgr.shape[:2]
        render_key = (img_w, img_h, canvas_w, canvas_h)

        # Proportional fit scale to keep image aspect ratio with workspace padding around image.
        usable_w = max(1, canvas_w - 2 * IMAGE_CANVAS_PADDING)
        usable_h = max(1, canvas_h - 2 * IMAGE_CANVAS_PADDING)
        self.display_scale = min(usable_w / img_w, usable_h / img_h)
        self.display_w = int(img_w * self.display_scale)
        self.display_h = int(img_h * self.display_scale)
        self.image_offset_x = (canvas_w - self.display_w) // 2
        self.image_offset_y = (canvas_h - self.display_h) // 2

        # Expensive image resize/conversion happens only when canvas/image size changes.
        if self.last_render_key != render_key or self.base_image_item is None:
            rgb = cv2.cvtColor(self.original_bgr, cv2.COLOR_BGR2RGB)
            pil_img = Image.fromarray(rgb).resize((self.display_w, self.display_h), Image.LANCZOS)
            self.display_photo = ImageTk.PhotoImage(pil_img)

            if self.base_image_item is None:
                self.base_image_item = self.canvas.create_image(
                    self.image_offset_x,
                    self.image_offset_y,
                    image=self.display_photo,
                    anchor="nw",
                    tags=("base_image",),
                )
            else:
                self.canvas.coords(self.base_image_item, self.image_offset_x, self.image_offset_y)
                self.canvas.itemconfig(self.base_image_item, image=self.display_photo)
            self.last_render_key = render_key

        self._draw_overlays()

    def _schedule_overlay_redraw(self, delay_ms=12):
        """Throttle overlay redraw to keep mouse interaction smooth."""
        if self.overlay_redraw_job is not None:
            return
        self.overlay_redraw_job = self.root.after(delay_ms, self._run_overlay_redraw)

    def _run_overlay_redraw(self):
        self.overlay_redraw_job = None
        self._draw_overlays()

    def _draw_overlays(self):
        """Redraw only vector overlays, keeping base image unchanged."""
        self.canvas.delete("overlay")
        self._draw_boundary_overlay()
        self._draw_center_overlay()
        self._draw_cardinal_overlay()
        self._draw_zones_overlay()

    # ------------------------------
    # Coordinate conversion helpers
    # ------------------------------
    def _canvas_to_image(self, x_canvas: float, y_canvas: float):
        """Convert canvas coordinates to original image coordinates."""
        if self.original_bgr is None:
            return None

        x = (x_canvas - self.image_offset_x) / self.display_scale
        y = (y_canvas - self.image_offset_y) / self.display_scale

        img_h, img_w = self.original_bgr.shape[:2]
        if x < 0 or y < 0 or x >= img_w or y >= img_h:
            return None
        return (float(x), float(y))

    def _image_to_canvas(self, x_img: float, y_img: float):
        """Convert original image coordinates to canvas coordinates."""
        x = x_img * self.display_scale + self.image_offset_x
        y = y_img * self.display_scale + self.image_offset_y
        return (x, y)

    # ------------------------------
    # Boundary drawing
    # ------------------------------
    def _on_canvas_click(self, event):
        """Handle click to append boundary vertex while polygon is open in manual mode."""
        if self.original_bgr is None:
            return

        if self.boundary_mode.get() != "manual":
            self.status_var.set("Manual point marking is disabled in Automated mode.")
            return

        target = self.active_boundary_target.get()
        active_points = self.boundary_points if target == "center" else self.barchart_boundary_points
        active_closed = self.polygon_closed if target == "center" else self.barchart_polygon_closed

        if active_closed:
            self.status_var.set(f"{target.title()} boundary already closed. Clear to redraw.")
            return

        img_point = self._canvas_to_image(event.x, event.y)
        if img_point is None:
            return

        active_points.append(img_point)
        self._render_canvas()
        self.status_var.set(f"{target.title()} boundary points: {len(active_points)}")

    def _on_canvas_motion(self, event):
        """Track cursor to draw a live guide line from last point to current mouse position."""
        if self.original_bgr is None:
            return
        if self.boundary_mode.get() != "manual" or self.polygon_closed:
            # Only block center preview on closed center polygon.
            if self.active_boundary_target.get() == "center":
                return
        active_points = self.boundary_points if self.active_boundary_target.get() == "center" else self.barchart_boundary_points
        if self.active_boundary_target.get() == "barchart" and self.barchart_polygon_closed:
            return
        if not active_points:
            return

        self.cursor_img_point = self._canvas_to_image(event.x, event.y)
        self._schedule_overlay_redraw()

    def _on_canvas_leave(self, _event):
        """Hide live guide line when cursor leaves canvas area."""
        if self.cursor_img_point is not None:
            self.cursor_img_point = None
            self._draw_overlays()

    def _draw_boundary_overlay(self):
        """Draw center boundary and barchart boundary overlays."""
        def draw_polygon(points, point_color, line_color, closed, line_width):
            if not points:
                return
            radius = 4
            for px, py in points:
                cx, cy = self._image_to_canvas(px, py)
                self.canvas.create_oval(
                    cx - radius,
                    cy - radius,
                    cx + radius,
                    cy + radius,
                    fill=point_color,
                    outline=point_color,
                    tags=("overlay",),
                )
            if len(points) >= 2:
                for i in range(1, len(points)):
                    x1, y1 = self._image_to_canvas(*points[i - 1])
                    x2, y2 = self._image_to_canvas(*points[i])
                    self.canvas.create_line(x1, y1, x2, y2, fill=line_color, width=line_width, tags=("overlay",))
                if closed and len(points) >= 3:
                    x1, y1 = self._image_to_canvas(*points[-1])
                    x2, y2 = self._image_to_canvas(*points[0])
                    self.canvas.create_line(x1, y1, x2, y2, fill=line_color, width=line_width, tags=("overlay",))

        draw_polygon(self.boundary_points, BOUNDARY_POINT_COLOR, BOUNDARY_LINE_COLOR, self.polygon_closed, 2)
        draw_polygon(
            self.barchart_boundary_points,
            BARCHART_BOUNDARY_POINT_COLOR,
            BARCHART_BOUNDARY_LINE_COLOR,
            self.barchart_polygon_closed,
            2,
        )

        # Live guide line for whichever boundary target is active.
        active_target = self.active_boundary_target.get()
        active_points = self.boundary_points if active_target == "center" else self.barchart_boundary_points
        active_closed = self.polygon_closed if active_target == "center" else self.barchart_polygon_closed
        guide_color = BOUNDARY_LINE_COLOR if active_target == "center" else BARCHART_BOUNDARY_LINE_COLOR
        if self.boundary_mode.get() == "manual" and not active_closed and len(active_points) >= 1 and self.cursor_img_point is not None:
            x1, y1 = self._image_to_canvas(*active_points[-1])
            x2, y2 = self._image_to_canvas(*self.cursor_img_point)
            self.canvas.create_line(x1, y1, x2, y2, fill=guide_color, width=1, dash=(4, 2), tags=("overlay",))

    def auto_detect_boundary(self):
        """
        Detect plot boundary from image using OpenCV edge/contour workflow.
        Picks the largest external contour as boundary for this simple version.
        """
        if self.original_bgr is None:
            messagebox.showwarning("Warning", "Please upload an image first.")
            return

        gray = cv2.cvtColor(self.original_bgr, cv2.COLOR_BGR2GRAY)
        blur = cv2.GaussianBlur(gray, (5, 5), 0)
        edges = cv2.Canny(blur, 50, 150)
        edges = cv2.dilate(edges, np.ones((3, 3), dtype=np.uint8), iterations=1)

        contours, _ = cv2.findContours(edges, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
        if not contours:
            messagebox.showerror("Boundary Detection", "No boundary contour detected.")
            return

        largest = max(contours, key=cv2.contourArea)
        if cv2.contourArea(largest) <= 1.0:
            messagebox.showerror("Boundary Detection", "Detected contour is too small.")
            return

        # Approximate contour to reduce point count while preserving shape.
        peri = cv2.arcLength(largest, True)
        approx = cv2.approxPolyDP(largest, 0.01 * peri, True)
        contour_pts = approx.reshape(-1, 2) if len(approx) >= 3 else largest.reshape(-1, 2)

        if len(contour_pts) < 3:
            messagebox.showerror("Boundary Detection", "Could not extract a valid polygon boundary.")
            return

        detected_points = [(float(x), float(y)) for x, y in contour_pts]
        target = self.active_boundary_target.get()
        if target == "center":
            self.boundary_points = detected_points
            self.polygon_closed = False
            self.center_point = None
            self.zones_drawn = False
        else:
            self.barchart_boundary_points = detected_points
            self.barchart_polygon_closed = False
        self.cursor_img_point = None
        self._render_canvas()
        self.status_var.set(
            f"Auto {target} boundary detected with {len(detected_points)} points."
        )

    # ------------------------------
    # Center / geometry calculations
    # ------------------------------
    def mark_center(self):
        """Close polygon and compute geometric centroid using polygon centroid formula."""
        if self.original_bgr is None:
            messagebox.showwarning("Warning", "Please upload an image first.")
            return

        if len(self.boundary_points) < 3:
            messagebox.showwarning("Warning", "Mark at least 3 boundary points.")
            return

        self.polygon_closed = True
        centroid = self._polygon_centroid(self.boundary_points)
        if centroid is None:
            messagebox.showerror(
                "Error",
                "Could not compute centroid. Polygon area appears too small or invalid.",
            )
            return

        self.center_point = centroid
        self._render_canvas()

        # Ask north tilt after center is marked.
        self._ask_north_tilt()
        self.status_var.set(
            f"Center marked at ({self.center_point[0]:.1f}, {self.center_point[1]:.1f})."
        )

    def _polygon_centroid(self, points):
        """
        Compute centroid (Cx, Cy) of a polygon using the area-weighted centroid formula.
        Also called the geometric center for a simple polygon.
        """
        area2 = 0.0
        cx_acc = 0.0
        cy_acc = 0.0
        n = len(points)

        for i in range(n):
            x1, y1 = points[i]
            x2, y2 = points[(i + 1) % n]
            cross = x1 * y2 - x2 * y1
            area2 += cross
            cx_acc += (x1 + x2) * cross
            cy_acc += (y1 + y2) * cross

        if abs(area2) < 1e-9:
            return None

        cx = cx_acc / (3.0 * area2)
        cy = cy_acc / (3.0 * area2)
        return (cx, cy)

    def _draw_center_overlay(self):
        """Draw a visible center marker as a cross (+)."""
        if self.center_point is None:
            return

        cx, cy = self._image_to_canvas(*self.center_point)
        half = 10
        self.canvas.create_line(cx - half, cy, cx + half, cy, fill=CENTER_COLOR, width=3, tags=("overlay",))
        self.canvas.create_line(cx, cy - half, cx, cy + half, fill=CENTER_COLOR, width=3, tags=("overlay",))

    # ------------------------------
    # North tilt
    # ------------------------------
    def _ask_north_tilt(self):
        """Prompt user for north tilt angle in degrees and store it."""
        angle = simpledialog.askfloat(
            "North Tilt",
            "Enter North tilt angle (degrees).\nPositive = clockwise, Negative = anticlockwise",
            initialvalue=self.north_tilt_deg,
        )
        if angle is not None:
            self.north_tilt_deg = float(angle)

    def set_north_tilt(self):
        """Button handler to update north tilt anytime."""
        self._ask_north_tilt()
        self.status_var.set(f"North tilt set to {self.north_tilt_deg:.2f} degrees.")
        if self.zones_drawn or self.cardinal_drawn:
            self._render_canvas()

    # ------------------------------
    # Cardinal lines (N/S/E/W)
    # ------------------------------
    def mark_cardinal_lines(self):
        """Draw N, S, E, W lines from center to boundary using north tilt as reference."""
        if self.center_point is None:
            messagebox.showwarning("Warning", "Please mark center first.")
            return
        if len(self.boundary_points) < 3:
            messagebox.showwarning("Warning", "Please mark/detect plot boundary first.")
            return

        self.cardinal_drawn = True
        self._render_canvas()
        self.status_var.set("N/S/E/W lines drawn up to boundary.")

    def _draw_cardinal_overlay(self):
        """Draw cardinal direction lines clipped to boundary and put N/S/E/W labels."""
        if not self.cardinal_drawn or self.center_point is None:
            return

        # Cardinal directions are spaced by 90 degrees from North.
        cardinal_angles = {
            "N": self.north_tilt_deg,
            "E": self.north_tilt_deg + 90.0,
            "S": self.north_tilt_deg + 180.0,
            "W": self.north_tilt_deg + 270.0,
        }

        cx_canvas, cy_canvas = self._image_to_canvas(*self.center_point)
        for label, ang in cardinal_angles.items():
            end_img = self._ray_boundary_intersection(self.center_point, ang)
            if end_img is None:
                continue
            ex, ey = self._image_to_canvas(*end_img)
            self.canvas.create_line(
                cx_canvas, cy_canvas, ex, ey, fill=CARDINAL_LINE_COLOR, width=2, dash=(7, 3)
                ,tags=("overlay",)
            )

            # Put label slightly inward from boundary for readability.
            lx = cx_canvas + 0.9 * (ex - cx_canvas)
            ly = cy_canvas + 0.9 * (ey - cy_canvas)
            self.canvas.create_text(
                lx,
                ly,
                text=label,
                fill=CARDINAL_TEXT_COLOR,
                font=("Helvetica", 11, "bold"),
                tags=("overlay",),
            )

    # ------------------------------
    # 16 zone drawing
    # ------------------------------
    def mark_16_zones(self):
        """Draw 16 directional sectors (22.5 deg each) from center with labels."""
        if self.center_point is None:
            messagebox.showwarning("Warning", "Please mark center first.")
            return
        if len(self.boundary_points) < 3:
            messagebox.showwarning("Warning", "Please mark/detect plot boundary first.")
            return

        self.zones_drawn = True
        self._render_canvas()
        self.status_var.set("16 directional zones drawn with lines extended to boundary.")

    def mark_devta(self):
        """Placeholder action for upcoming Devta marking logic."""
        messagebox.showinfo(
            "Mark Devta",
            "Devta marking is ready for integration. Share the calculation logic and I will implement it.",
        )

    def _draw_zones_overlay(self):
        """
        Draw radial lines and direction labels with north tilt rotation.
        Each radial line is clipped so it ends exactly at polygon boundary.
        """
        if not self.zones_drawn or self.center_point is None:
            return

        cx_img, cy_img = self.center_point
        cx_canvas, cy_canvas = self._image_to_canvas(cx_img, cy_img)

        # In image/canvas coordinates: +y is down, so for clockwise positive input
        # we rotate displayed directions by adding tilt to each base angle.
        step = 360.0 / 16.0  # 22.5 degrees

        # Zone model aligned to Mahavastu wheel style:
        # - Zone names (N, NNE, NE, ...) are center angles.
        # - Boundary rays are +/- 11.25° around each center.
        start_boundary_deg = self.north_tilt_deg - (step / 2.0)

        # Draw 16 boundary rays clipped to the plot boundary.
        for i in range(16):
            deg = start_boundary_deg + i * step
            end_img = self._ray_boundary_intersection(self.center_point, deg)
            if end_img is None:
                # Fallback when no intersection is found (unexpected for valid center/polygon).
                rad = math.radians(deg)
                fx = cx_img + 2.0 * max(self.display_w, self.display_h) * math.sin(rad)
                fy = cy_img - 2.0 * max(self.display_w, self.display_h) * math.cos(rad)
                end_img = (fx, fy)
            x_end, y_end = self._image_to_canvas(*end_img)

            self.canvas.create_line(
                cx_canvas,
                cy_canvas,
                x_end,
                y_end,
                fill=ZONE_LINE_COLOR,
                width=1,
                tags=("overlay",),
            )

        # Place labels at each zone center angle.
        for i, name in enumerate(self.ZONE_NAMES):
            mid_deg = self.north_tilt_deg + i * step
            mid_hit = self._ray_boundary_intersection(self.center_point, mid_deg)
            if mid_hit is None:
                continue

            # Keep text safely inside the polygon by using a fraction of center-to-boundary distance.
            x_txt_img = cx_img + 0.62 * (mid_hit[0] - cx_img)
            y_txt_img = cy_img + 0.62 * (mid_hit[1] - cy_img)
            x_txt, y_txt = self._image_to_canvas(x_txt_img, y_txt_img)

            self.canvas.create_text(
                x_txt,
                y_txt,
                text=name,
                fill=ZONE_TEXT_COLOR,
                font=("Helvetica", 10, "bold"),
                tags=("overlay",),
            )

    def _ray_boundary_intersection(self, origin, angle_deg):
        """
        Return nearest intersection point between a ray and polygon boundary.

        Ray:
            P = origin + t * d, t >= 0
        Polygon edge:
            Q = a + u * (b - a), 0 <= u <= 1
        """
        if len(self.boundary_points) < 2:
            return None

        ox, oy = origin
        rad = math.radians(angle_deg)
        dx = math.sin(rad)
        dy = -math.cos(rad)  # 0 deg points to North in image coordinates.

        nearest_t = None
        nearest_pt = None
        eps = 1e-9

        for i in range(len(self.boundary_points)):
            ax, ay = self.boundary_points[i]
            bx, by = self.boundary_points[(i + 1) % len(self.boundary_points)]
            sx = bx - ax
            sy = by - ay

            # Solve:
            # ox + t*dx = ax + u*sx
            # oy + t*dy = ay + u*sy
            # Using 2D cross-product form for robustness.
            denom = dx * sy - dy * sx
            if abs(denom) < eps:
                continue

            rx = ax - ox
            ry = ay - oy
            t = (rx * sy - ry * sx) / denom
            u = (rx * dy - ry * dx) / denom

            if t >= 0.0 and -eps <= u <= 1.0 + eps:
                ix = ox + t * dx
                iy = oy + t * dy
                if nearest_t is None or t < nearest_t:
                    nearest_t = t
                    nearest_pt = (ix, iy)

        return nearest_pt

    # ------------------------------
    # Area calculations
    # ------------------------------
    def calculate_plot_area(self):
        """Calculate polygon area with shoelace formula and display result."""
        if len(self.boundary_points) < 3:
            messagebox.showwarning("Warning", "Please mark at least 3 boundary points.")
            return

        area = self._polygon_area(self.boundary_points)
        messagebox.showinfo("Center Boundary Area", f"Center boundary area: {area:.2f} square-pixels")

    def _polygon_area(self, points):
        """
        Shoelace formula for polygon area.
        Area is in image pixel units (square-pixels) for this version.
        """
        pts = np.array(points, dtype=np.float64)
        x = pts[:, 0]
        y = pts[:, 1]
        area = 0.5 * abs(np.dot(x, np.roll(y, -1)) - np.dot(y, np.roll(x, -1)))
        return float(area)

    def calculate_zone_areas(self):
        """
        Calculate each zone area by intersecting:
        (plot polygon mask) AND (zone wedge mask from center between two rays).
        This yields different areas for different zones based on actual geometry.
        """
        barchart_points = self.barchart_boundary_points if len(self.barchart_boundary_points) >= 3 else self.boundary_points
        if len(barchart_points) < 3 or self.center_point is None:
            messagebox.showwarning(
                "Warning",
                "Please ensure boundary is marked and center is set before zone area calculation.",
            )
            return

        zone_areas = self._compute_zone_areas_mask_based(barchart_points)
        total_area = self._polygon_area(barchart_points)
        sum_zone_area = sum(zone_areas)
        self.zone_areas_cache = zone_areas
        if barchart_points is self.barchart_boundary_points and len(self.barchart_boundary_points) >= 3:
            self.barchart_polygon_closed = True
            self._render_canvas()

        lines = [
            f"Total polygon area (shoelace): {total_area:.2f} sq-pixels",
            f"Total zonal area (mask sum): {sum_zone_area:.2f} sq-pixels",
            "",
            "Zone areas:",
        ]
        for name, area in zip(self.ZONE_NAMES, zone_areas):
            lines.append(f"{name}: {area:.2f} sq-pixels")

        messagebox.showinfo("16 Zone Areas", "\n".join(lines))

    def _compute_zone_areas_mask_based(self, polygon_points):
        """
        Build binary masks and measure pixel area for each angular zone.

        Steps:
        1) Fill polygon mask for the plot boundary.
        2) For each zone, create a large triangle (center, ray1 far point, ray2 far point).
        3) Intersect triangle mask with polygon mask.
        4) Count non-zero pixels as zone area.
        """
        img_h, img_w = self.original_bgr.shape[:2]
        polygon_mask = np.zeros((img_h, img_w), dtype=np.uint8)
        poly = np.array(polygon_points, dtype=np.int32)
        cv2.fillPoly(polygon_mask, [poly], 255)

        cx, cy = self.center_point
        step = 360.0 / 16.0
        # Keep zone centers at N, NNE, NE... and wedge boundaries at +/- 11.25°.
        start_boundary_deg = self.north_tilt_deg - (step / 2.0)
        far_r = math.hypot(img_w, img_h) * 2.0

        zone_areas = []
        for i in range(16):
            a1 = start_boundary_deg + i * step
            a2 = start_boundary_deg + (i + 1) * step

            # Two far points make an effectively infinite wedge within image extent.
            p1 = (cx + far_r * math.sin(math.radians(a1)), cy - far_r * math.cos(math.radians(a1)))
            p2 = (cx + far_r * math.sin(math.radians(a2)), cy - far_r * math.cos(math.radians(a2)))

            wedge_mask = np.zeros((img_h, img_w), dtype=np.uint8)
            tri = np.array([[cx, cy], [p1[0], p1[1]], [p2[0], p2[1]]], dtype=np.int32)
            cv2.fillConvexPoly(wedge_mask, tri, 255)

            zone_mask = cv2.bitwise_and(polygon_mask, wedge_mask)
            zone_area = float(cv2.countNonZero(zone_mask))
            zone_areas.append(zone_area)

        return zone_areas

    @staticmethod
    def _hex_to_bgr(color_hex):
        """Convert #RRGGBB color string to OpenCV BGR tuple."""
        color_hex = color_hex.lstrip("#")
        if len(color_hex) != 6:
            return (0, 255, 0)
        r = int(color_hex[0:2], 16)
        g = int(color_hex[2:4], 16)
        b = int(color_hex[4:6], 16)
        return (b, g, r)

    def _create_marked_image_for_pdf(self, output_path):
        """
        Create an export image with plot markings:
        boundary, center, N/S/E/W lines, and 16 zone rays clipped to boundary.
        """
        img = self.original_bgr.copy()
        img_h, img_w = img.shape[:2]
        # Scale drawing sizes with image resolution so labels/lines stay readable in PDF.
        scale_factor = max(0.8, min(1.8, max(img_w, img_h) / 900.0))
        point_color = self._hex_to_bgr(BOUNDARY_POINT_COLOR)
        boundary_color = self._hex_to_bgr(BOUNDARY_LINE_COLOR)
        center_color = self._hex_to_bgr(CENTER_COLOR)
        zone_color = self._hex_to_bgr(ZONE_LINE_COLOR)
        cardinal_color = self._hex_to_bgr(CARDINAL_LINE_COLOR)

        # Draw boundary polygon and vertices.
        if len(self.boundary_points) >= 2:
            for i in range(1, len(self.boundary_points)):
                p1 = tuple(np.int32(self.boundary_points[i - 1]))
                p2 = tuple(np.int32(self.boundary_points[i]))
                cv2.line(img, p1, p2, boundary_color, 2, cv2.LINE_AA)
            if self.polygon_closed and len(self.boundary_points) >= 3:
                p1 = tuple(np.int32(self.boundary_points[-1]))
                p2 = tuple(np.int32(self.boundary_points[0]))
                cv2.line(img, p1, p2, boundary_color, 2, cv2.LINE_AA)

        for p in self.boundary_points:
            pt = tuple(np.int32(p))
            cv2.circle(img, pt, 4, point_color, -1, cv2.LINE_AA)

        # Draw center cross.
        if self.center_point is not None:
            cx, cy = (int(round(self.center_point[0])), int(round(self.center_point[1])))
            cv2.line(img, (cx - 12, cy), (cx + 12, cy), center_color, 2, cv2.LINE_AA)
            cv2.line(img, (cx, cy - 12), (cx, cy + 12), center_color, 2, cv2.LINE_AA)

            # Draw cardinal lines (N/S/E/W) up to boundary.
            for label, ang in {
                "N": self.north_tilt_deg,
                "E": self.north_tilt_deg + 90.0,
                "S": self.north_tilt_deg + 180.0,
                "W": self.north_tilt_deg + 270.0,
            }.items():
                hit = self._ray_boundary_intersection(self.center_point, ang)
                if hit is None:
                    continue
                end = (int(round(hit[0])), int(round(hit[1])))
                cv2.line(img, (cx, cy), end, cardinal_color, 2, cv2.LINE_AA)
                tx = int(round(cx + 0.9 * (end[0] - cx)))
                ty = int(round(cy + 0.9 * (end[1] - cy)))
                cv2.putText(
                    img, label, (tx, ty), cv2.FONT_HERSHEY_SIMPLEX, 0.5, cardinal_color, 2, cv2.LINE_AA
                )

            # Draw 16 zone boundary rays (clipped to boundary).
            # Boundaries are shifted by half-sector so zone names stay centered on compass angles.
            step = 360.0 / 16.0
            start_boundary_deg = self.north_tilt_deg - (step / 2.0)
            for i in range(16):
                ang = start_boundary_deg + i * step
                hit = self._ray_boundary_intersection(self.center_point, ang)
                if hit is None:
                    continue
                end = (int(round(hit[0])), int(round(hit[1])))
                # Double-stroke for visibility on mixed-color backgrounds.
                cv2.line(img, (cx, cy), end, (255, 255, 255), max(2, int(3 * scale_factor)), cv2.LINE_AA)
                cv2.line(img, (cx, cy), end, zone_color, max(1, int(2 * scale_factor)), cv2.LINE_AA)

            # Write zone names in black at zone-center directions.
            for i, zone_name in enumerate(self.ZONE_NAMES):
                zone_center_deg = self.north_tilt_deg + i * step
                hit = self._ray_boundary_intersection(self.center_point, zone_center_deg)
                if hit is None:
                    continue
                tx = int(round(cx + 0.68 * (hit[0] - cx)))
                ty = int(round(cy + 0.68 * (hit[1] - cy)))
                # Increase/decrease zone-name font size by changing this value (1.00 -> bigger/smaller).
                zone_label_font_scale = 1.00 * scale_factor
                # White under-stroke for readability on dark areas, then black text on top.
                cv2.putText(
                    img,
                    zone_name,
                    (tx, ty),
                    cv2.FONT_HERSHEY_SIMPLEX,
                    zone_label_font_scale,
                    (255, 255, 255),
                    max(3, int(5 * scale_factor)),
                    cv2.LINE_AA,
                )
                cv2.putText(
                    img,
                    zone_name,
                    (tx, ty),
                    cv2.FONT_HERSHEY_SIMPLEX,
                    zone_label_font_scale,
                    (0, 0, 0),
                    max(1, int(2 * scale_factor)),
                    cv2.LINE_AA,
                )

        cv2.imwrite(output_path, img)

    def _create_gridded_image_for_pdf(self, output_path, rows=9, cols=9):
        """
        Create a gridded version of the image (Mahavastu style 9x9 default).
        Also includes boundary and center overlays for easier reading.
        """
        img = self.original_bgr.copy()
        h, w = img.shape[:2]
        grid_color = (180, 180, 180)
        boundary_color = self._hex_to_bgr(BOUNDARY_LINE_COLOR)
        center_color = self._hex_to_bgr(CENTER_COLOR)

        # Draw full-image rectangular grid.
        for c in range(1, cols):
            x = int(round((c / cols) * w))
            cv2.line(img, (x, 0), (x, h - 1), grid_color, 1, cv2.LINE_AA)
        for r in range(1, rows):
            y = int(round((r / rows) * h))
            cv2.line(img, (0, y), (w - 1, y), grid_color, 1, cv2.LINE_AA)

        # Overlay boundary for context.
        if len(self.boundary_points) >= 2:
            for i in range(1, len(self.boundary_points)):
                p1 = tuple(np.int32(self.boundary_points[i - 1]))
                p2 = tuple(np.int32(self.boundary_points[i]))
                cv2.line(img, p1, p2, boundary_color, 2, cv2.LINE_AA)
            if self.polygon_closed and len(self.boundary_points) >= 3:
                p1 = tuple(np.int32(self.boundary_points[-1]))
                p2 = tuple(np.int32(self.boundary_points[0]))
                cv2.line(img, p1, p2, boundary_color, 2, cv2.LINE_AA)

        if self.center_point is not None:
            cx, cy = (int(round(self.center_point[0])), int(round(self.center_point[1])))
            cv2.line(img, (cx - 10, cy), (cx + 10, cy), center_color, 2, cv2.LINE_AA)
            cv2.line(img, (cx, cy - 10), (cx, cy + 10), center_color, 2, cv2.LINE_AA)

        cv2.imwrite(output_path, img)

    def _show_progress_popup(self, title="Please wait", initial_text="Preparing..."):
        """Show modal progress popup used during PDF export."""
        if self.progress_win is not None and self.progress_win.winfo_exists():
            self._close_progress_popup()

        self.progress_value_var.set(0.0)
        self.progress_label_var.set(initial_text)

        self.progress_win = tk.Toplevel(self.root)
        self.progress_win.title(title)
        self.progress_win.transient(self.root)
        self.progress_win.grab_set()
        self.progress_win.resizable(False, False)

        frame = tk.Frame(self.progress_win, padx=14, pady=14)
        frame.pack(fill="both", expand=True)
        tk.Label(frame, textvariable=self.progress_label_var, anchor="w").pack(fill="x", pady=(0, 8))

        pb = ttk.Progressbar(
            frame,
            orient="horizontal",
            length=320,
            mode="determinate",
            variable=self.progress_value_var,
            maximum=100.0,
        )
        pb.pack(fill="x")

        # Keep popup centered and responsive.
        self.progress_win.update_idletasks()
        x = self.root.winfo_rootx() + (self.root.winfo_width() // 2) - 180
        y = self.root.winfo_rooty() + (self.root.winfo_height() // 2) - 45
        self.progress_win.geometry(f"+{max(x, 0)}+{max(y, 0)}")

    def _update_progress_popup(self, value, text):
        """Update progress bar value/text and refresh UI immediately."""
        if self.progress_win is None or not self.progress_win.winfo_exists():
            return
        self.progress_value_var.set(float(value))
        self.progress_label_var.set(text)
        self.progress_win.update_idletasks()
        self.root.update()

    def _close_progress_popup(self):
        """Close export progress popup if it exists."""
        if self.progress_win is not None and self.progress_win.winfo_exists():
            self.progress_win.grab_release()
            self.progress_win.destroy()
        self.progress_win = None

    # ------------------------------
    # PDF export using existing Mahavastu bar-chart logic
    # ------------------------------
    def export_pdf_report(self):
        """
        Export a 3-page PDF report:
        Page 1: Zonal bar chart + zonal table + LOB/ULOB/LLOB
        Page 2: Prakriti bar chart
        Page 3: Plot image with marked 16 zones

        This follows the same core logic used in Prakartibarchart.py.
        """
        if len(self.boundary_points) < 3 or self.center_point is None:
            messagebox.showwarning(
                "Warning",
                "Please mark boundary and center first before exporting report.",
            )
            return

        barchart_points = self.barchart_boundary_points if len(self.barchart_boundary_points) >= 3 else self.boundary_points

        # Use cached zone areas if available, otherwise compute fresh values.
        zone_areas = self.zone_areas_cache
        if zone_areas is None or len(zone_areas) != 16:
            zone_areas = self._compute_zone_areas_mask_based(barchart_points)
            self.zone_areas_cache = zone_areas
        if barchart_points is self.barchart_boundary_points and len(self.barchart_boundary_points) >= 3:
            self.barchart_polygon_closed = True

        zone_data = {z: float(a) for z, a in zip(self.ZONE_NAMES, zone_areas)}

        # Balance line calculations (same logic as your bar-chart script).
        areas = list(zone_data.values())
        lob = sum(areas) / len(areas)
        ulob = (lob + max(areas)) / 2.0
        llob = (lob + min(areas)) / 2.0

        # Remarks based on ULOB/LLOB thresholds.
        remarks = {}
        for z, v in zone_data.items():
            if v > ulob:
                remarks[z] = "High"
            elif v < llob:
                remarks[z] = "Low"
            else:
                remarks[z] = "Balanced"

        # Same prakriti grouping as existing script.
        prakriti_map = {
            "Fire": ["E", "ESE", "SE", "SSE", "S", "SSW"],
            "Water": ["NNW", "N", "NNE", "NE", "ENE"],
            "Air": ["SW", "WSW", "W", "WNW", "NW"],
        }
        prakriti_colors = {
            "Fire": "#ffcccb",
            "Water": "#cce5ff",
            "Air": "#d5f5e3",
        }

        prakriti_strength = {
            p: sum(zone_data[z] for z in zlist) for p, zlist in prakriti_map.items()
        }
        total_prakriti = sum(prakriti_strength.values())
        if total_prakriti <= 0:
            messagebox.showerror("Export Error", "Prakriti total is zero. Cannot generate chart.")
            return

        prakriti_percentage = {
            p: (v / total_prakriti) * 100.0 for p, v in prakriti_strength.items()
        }
        prakriti_sorted = sorted(prakriti_strength.items(), key=lambda x: x[1], reverse=True)
        final_prakriti = "-".join(p[0] for p in prakriti_sorted)

        pdf_path = filedialog.asksaveasfilename(
            title="Save Mahavastu PDF Report",
            defaultextension=".pdf",
            filetypes=[("PDF files", "*.pdf")],
            initialfile="Mahavastu_Zonal_Report.pdf",
        )
        if not pdf_path:
            return

        # Create temporary files for chart images, then embed into PDF.
        zone_chart_path = None
        prakriti_chart_path = None
        marked_image_path = None
        self._show_progress_popup(title="Generating PDF", initial_text="Initializing export...")
        try:
            self._update_progress_popup(8, "Creating temporary files...")
            with tempfile.NamedTemporaryFile(suffix="_zone_chart.png", delete=False) as t1:
                zone_chart_path = t1.name
            with tempfile.NamedTemporaryFile(suffix="_prakriti_chart.png", delete=False) as t2:
                prakriti_chart_path = t2.name
            with tempfile.NamedTemporaryFile(suffix="_marked_plot.png", delete=False) as t3:
                marked_image_path = t3.name

            # -------- Chart 1: Zonal areas --------
            self._update_progress_popup(24, "Building zonal bar chart...")
            plt.figure(figsize=(12, 6))
            plt.bar(self.ZONE_NAMES, areas, color="#aed6f1", edgecolor="black")
            plt.axhline(lob, color="blue", linestyle="--", linewidth=2)
            plt.axhline(ulob, color="red", linestyle="--", linewidth=2)
            plt.axhline(llob, color="orange", linestyle="--", linewidth=2)
            plt.title("MahaVastu Zonal Strength Analysis")
            plt.xlabel("16 Zones")
            plt.ylabel("Area / Strength")
            # Keep LOB text separate from x-axis zone labels for a clean format.
            plt.text(
                0.985,
                0.965,
                f"LOB: {lob:.1f}\nULOB: {ulob:.1f}\nLLOB: {llob:.1f}",
                transform=plt.gca().transAxes,
                ha="right",
                va="top",
                fontsize=9,
                bbox={"facecolor": "white", "alpha": 0.85, "edgecolor": "#9ca3af"},
            )
            plt.savefig(zone_chart_path, dpi=300, bbox_inches="tight")
            plt.close()

            # -------- Chart 2: Prakriti --------
            self._update_progress_popup(40, "Building prakriti bar chart...")
            plt.figure(figsize=(7, 5))
            bars = plt.bar(
                list(prakriti_strength.keys()),
                list(prakriti_strength.values()),
                color=[prakriti_colors[k] for k in prakriti_strength],
                edgecolor="black",
            )
            for bar, val in zip(bars, prakriti_strength.values()):
                plt.text(
                    bar.get_x() + bar.get_width() / 2,
                    bar.get_height(),
                    f"{val:.0f}",
                    ha="center",
                    va="bottom",
                    fontsize=11,
                    fontweight="bold",
                )
            plt.title("Mahavastu Building Prakriti Bar Chart")
            plt.ylabel("Total Zonal Strength")
            plt.savefig(prakriti_chart_path, dpi=300, bbox_inches="tight")
            plt.close()

            # -------- Export images --------
            self._update_progress_popup(56, "Rendering marked zone image...")
            self._create_marked_image_for_pdf(marked_image_path)

            # -------- PDF pages --------
            self._update_progress_popup(72, "Composing PDF pages...")
            pdf = FPDF()
            pdf.set_auto_page_break(auto=False)

            # Page 1
            pdf.add_page()
            pdf.set_font("Arial", "B", 16)
            pdf.cell(0, 10, "MahaVastu Zonal Strength Report", ln=True, align="C")
            # Compact chart height prevents overlap with LOB/ULOB/LLOB text below.
            pdf.image(zone_chart_path, x=10, y=22, w=190, h=78)
            pdf.set_font("Arial", size=11)
            pdf.set_xy(10, 106)
            pdf.cell(0, 8, f"LOB (Line of Balance): {lob:.2f}", ln=True)
            pdf.set_x(10)
            pdf.cell(0, 8, f"ULOB (Upper Line of Balance): {ulob:.2f}", ln=True)
            pdf.set_x(10)
            pdf.cell(0, 8, f"LLOB (Lower Line of Balance): {llob:.2f}", ln=True)

            # Compact zone table (2 zones per row) to keep everything on page 1.
            pdf.ln(2)
            pdf.set_font("Arial", "B", 10)
            pdf.cell(25, 7, "Zone", 1, 0, "C")
            pdf.cell(24, 7, "Area", 1, 0, "C")
            pdf.cell(28, 7, "Remark", 1, 0, "C")
            pdf.cell(25, 7, "Zone", 1, 0, "C")
            pdf.cell(24, 7, "Area", 1, 0, "C")
            pdf.cell(28, 7, "Remark", 1, 1, "C")

            pdf.set_font("Arial", size=10)
            for i in range(8):
                z1 = self.ZONE_NAMES[i]
                z2 = self.ZONE_NAMES[i + 8]
                pdf.cell(25, 7, z1, 1, 0, "C")
                pdf.cell(24, 7, f"{zone_data[z1]:.0f}", 1, 0, "C")
                pdf.cell(28, 7, remarks[z1], 1, 0, "C")
                pdf.cell(25, 7, z2, 1, 0, "C")
                pdf.cell(24, 7, f"{zone_data[z2]:.0f}", 1, 0, "C")
                pdf.cell(28, 7, remarks[z2], 1, 1, "C")

            # Page 2
            pdf.add_page()
            pdf.set_font("Arial", "B", 16)
            pdf.cell(0, 10, "Mahavastu Prakriti Analysis", ln=True, align="C")
            pdf.image(prakriti_chart_path, x=20, y=24, w=170)
            pdf.set_xy(14, 175)
            pdf.set_font("Arial", "B", 12)
            pdf.cell(0, 8, "Element-wise Total Area", ln=True)
            pdf.set_font("Arial", size=11)
            pdf.cell(0, 7, f"Fire Area: {prakriti_strength['Fire']:.2f}", ln=True)
            pdf.cell(0, 7, f"Water Area: {prakriti_strength['Water']:.2f}", ln=True)
            pdf.cell(0, 7, f"Air Area: {prakriti_strength['Air']:.2f}", ln=True)
            pdf.ln(1)
            pdf.set_font("Arial", "B", 12)
            pdf.cell(0, 7, f"House Prakriti: {final_prakriti}", ln=True)
            pdf.set_font("Arial", size=11)
            for p in ["Fire", "Water", "Air"]:
                pdf.cell(0, 6, f"{p} Percentage: {prakriti_percentage[p]:.1f}%", ln=True)

            # Page 3
            pdf.add_page()
            pdf.set_font("Arial", "B", 16)
            pdf.cell(0, 10, "Plot with Marked 16 Zones", ln=True, align="C")
            pdf.image(marked_image_path, x=10, y=22, w=190)

            self._update_progress_popup(92, "Writing PDF to disk...")
            pdf.output(pdf_path)
            self._update_progress_popup(100, "Done.")
            messagebox.showinfo("Success", f"PDF exported successfully:\n{pdf_path}")

        except Exception as exc:
            messagebox.showerror("Export Error", f"Failed to export PDF:\n{exc}")
        finally:
            # Clean temporary chart files.
            if zone_chart_path and os.path.exists(zone_chart_path):
                os.remove(zone_chart_path)
            if prakriti_chart_path and os.path.exists(prakriti_chart_path):
                os.remove(prakriti_chart_path)
            if marked_image_path and os.path.exists(marked_image_path):
                os.remove(marked_image_path)
            self._close_progress_popup()

    # ------------------------------
    # Reset helpers
    # ------------------------------
    def clear_geometry_only(self):
        """Reset boundary/center/zones while keeping loaded image."""
        self.boundary_points = []
        self.barchart_boundary_points = []
        self.polygon_closed = False
        self.barchart_polygon_closed = False
        self.center_point = None
        self.zones_drawn = False
        self.cursor_img_point = None
        self.zone_areas_cache = None
        self.cardinal_drawn = False
        self.active_boundary_target.set("center")

    def clear_all(self):
        """Backward-compatible alias for full reset."""
        self.remove_image()

    def clear_markings(self):
        """Clear only markings/geometry while keeping uploaded image."""
        if self.original_bgr is None:
            self.status_var.set("No image loaded. Upload an image first.")
            return
        self.clear_geometry_only()
        self._render_canvas()
        self.status_var.set("All markings cleared. Image kept.")

    def remove_image(self):
        """Clear uploaded image and all drawn/derived data."""
        self.original_bgr = None
        self.display_photo = None
        self.clear_geometry_only()
        self.canvas.delete("all")
        self.status_var.set("Image removed. Load an image to begin.")


def show_startup_splash(root):
    """Show a short startup splash dialog for a software-like launch experience."""
    splash = tk.Toplevel(root)
    splash.title("Starting...")
    splash.geometry("420x220")
    splash.configure(bg="#0f172a")
    splash.overrideredirect(True)
    splash.attributes("-topmost", True)

    # Center splash on screen.
    screen_w = splash.winfo_screenwidth()
    screen_h = splash.winfo_screenheight()
    x = (screen_w // 2) - (420 // 2)
    y = (screen_h // 2) - (220 // 2)
    splash.geometry(f"420x220+{x}+{y}")

    container = tk.Frame(splash, bg="#0f172a", padx=20, pady=18)
    container.pack(fill="both", expand=True)
    tk.Label(
        container,
        text="Vastu Plot Analyzer",
        font=("Helvetica", 18, "bold"),
        fg="#f8fafc",
        bg="#0f172a",
    ).pack(pady=(8, 6))
    tk.Label(
        container,
        text="Loading modules and preparing workspace...",
        font=("Helvetica", 10),
        fg="#cbd5e1",
        bg="#0f172a",
    ).pack(pady=(0, 14))

    progress = ttk.Progressbar(container, mode="indeterminate", length=320)
    progress.pack(pady=(0, 10))
    progress.start(14)

    tk.Label(
        container,
        text="Please wait",
        font=("Helvetica", 9),
        fg="#94a3b8",
        bg="#0f172a",
    ).pack()

    return splash, progress


if __name__ == "__main__":
    app_root = tk.Tk()
    app_root.withdraw()
    splash_win, splash_progress = show_startup_splash(app_root)

    def start_main_app():
        splash_progress.stop()
        splash_win.destroy()
        app_root.deiconify()
        app_root.app = PlotAnalyzerApp(app_root)

    app_root.after(1400, start_main_app)
    app_root.mainloop()
